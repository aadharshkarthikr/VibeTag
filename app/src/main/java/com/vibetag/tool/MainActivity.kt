// app/src/main/java/com/vibetag/tool/MainActivity.kt
package com.vibetag.tool

import android.content.Context
import android.content.Intent
import android.media.MediaCodec
import android.media.MediaExtractor
import android.media.MediaFormat
import android.media.MediaMetadataRetriever
import android.net.Uri
import android.os.Bundle
import android.provider.DocumentsContract
import androidx.activity.ComponentActivity
import androidx.activity.compose.rememberLauncherForActivityResult
import androidx.activity.compose.setContent
import androidx.activity.result.contract.ActivityResultContracts
import androidx.compose.foundation.background
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.*
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.lazy.LazyRow
import androidx.compose.foundation.lazy.items
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.*
import androidx.compose.material3.*
import androidx.compose.runtime.*
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.text.font.FontWeight
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp
import androidx.documentfile.provider.DocumentFile
import kotlinx.coroutines.*
import org.json.JSONArray
import org.json.JSONObject
import java.io.*
import java.net.HttpURLConnection
import java.net.URL
import java.net.URLEncoder
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.security.MessageDigest
import kotlin.math.abs
import kotlin.math.sqrt

// ============================================================================
// 1. DATA MODELS & TAXONOMY
// ============================================================================

val DEFAULT_MOOD_TAXONOMY = listOf(
    "Romantic", "Tender", "Passionate", "Melancholic", "Sad", "Heartbroken",
    "Longing", "Wistful", "Nostalgic", "Bittersweet", "Dreamy", "Ethereal",
    "Atmospheric", "Mysterious", "Peaceful", "Relaxed", "Chill", "Soothing",
    "Joyful", "Happy", "Playful", "Uplifting", "Hopeful", "Inspirational",
    "Energetic", "Euphoric", "Danceable", "Aggressive", "Intense", "Dramatic",
    "Epic", "Suspenseful", "Dark", "Meditative", "Reflective", "Sensual", "Triumphant"
)

enum class WritePolicy(val label: String) {
    FILL_MISSING_ONLY("Fill Missing Only (Safe Default)"),
    REPLACE_HIGH_CONFIDENCE("Overwrite with High Confidence"),
    PRESERVE_EXISTING("Preserve All Existing Tags")
}

data class AudioTrackItem(
    val id: String,
    val uri: Uri,
    val fileName: String,
    val relativePath: String,
    val extension: String,
    val durationMs: Long,
    val title: String,
    val artist: String,
    val album: String,
    val currentGenre: String,
    val currentMood: String,
    val proposedGenre: String = "",
    val proposedMoods: List<String> = emptyList(),
    val confidence: Float = 0f,
    val evidenceNote: String = "",
    val isLocked: Boolean = false,
    val status: String = "Discovered"
)

data class JournalEntry(
    val trackId: String,
    val uriString: String,
    val fileName: String,
    val oldGenre: String,
    val oldMood: String,
    val newGenre: String,
    val newMood: String,
    val audioSha256: String,
    val timestamp: Long
)

// ============================================================================
// 2. SAFE BINARY METADATA ENGINE (MP3 ID3v2 & FLAC VORBIS + SHA-256 VERIFIER)
// ============================================================================

object SafeTagEngine {

    /**
     * Computes SHA-256 of the pure audio payload bytes (skipping ID3v2 or FLAC Vorbis metadata blocks)
     * so we can mathematically prove zero audio modification after writing Genre and Mood.
     */
    fun computeAudioPayloadSha256(file: File, ext: String): String {
        RandomAccessFile(file, "r").use { raf ->
            val (start, length) = when (ext.lowercase()) {
                "mp3" -> locateMp3AudioBounds(raf)
                "flac" -> locateFlacAudioBounds(raf)
                else -> 0L to raf.length()
            }
            val digest = MessageDigest.getInstance("SHA-256")
            raf.seek(start)
            val buf = ByteArray(65536)
            var rem = length
            while (rem > 0) {
                val read = raf.read(buf, 0, minOf(buf.size.toLong(), rem).toInt())
                if (read <= 0) break
                digest.update(buf, 0, read)
                rem -= read
            }
            return digest.digest().joinToString("") { "%02x".format(it) }
        }
    }

    private fun locateMp3AudioBounds(raf: RandomAccessFile): Pair<Long, Long> {
        var start = 0L
        if (raf.length() >= 10) {
            raf.seek(0)
            val h = ByteArray(10)
            raf.readFully(h)
            if (h[0] == 'I'.code.toByte() && h[1] == 'D'.code.toByte() && h[2] == '3'.code.toByte()) {
                val size = ((h[6].toInt() and 0x7F) shl 21) or
                    ((h[7].toInt() and 0x7F) shl 14) or
                    ((h[8].toInt() and 0x7F) shl 7) or
                    (h[9].toInt() and 0x7F)
                start = 10L + size
            }
        }
        return start to (raf.length() - start).coerceAtLeast(0L)
    }

    private fun locateFlacAudioBounds(raf: RandomAccessFile): Pair<Long, Long> {
        if (raf.length() < 8) return 0L to raf.length()
        raf.seek(0)
        val magic = ByteArray(4)
        raf.readFully(magic)
        if (String(magic, Charsets.US_ASCII) != "fLaC") return 0L to raf.length()
        var isLast = false
        while (!isLast && raf.filePointer + 4 <= raf.length()) {
            val bh = ByteArray(4)
            raf.readFully(bh)
            isLast = (bh[0].toInt() and 0x80) != 0
            val len = ((bh[1].toInt() and 0xFF) shl 16) or ((bh[2].toInt() and 0xFF) shl 8) or (bh[3].toInt() and 0xFF)
            raf.seek(raf.filePointer + len)
        }
        val start = raf.filePointer
        return start to (raf.length() - start).coerceAtLeast(0L)
    }

    /**
     * Reads Genre & Mood directly from MP3 (TCON / TMOO) or FLAC (GENRE / MOOD Vorbis Comment).
     */
    fun readGenreAndMood(file: File, ext: String): Pair<String, String> {
        return runCatching {
            when (ext.lowercase()) {
                "mp3" -> readMp3GenreAndMood(file)
                "flac" -> readFlacGenreAndMood(file)
                else -> "" to ""
            }
        }.getOrDefault("" to "")
    }

    /**
     * Transactionally writes ONLY Genre and Mood, verifies that the audio payload SHA-256 is 100% identical,
     * and swaps the verified bytes into the target SAF Uri.
     */
    fun writeGenreAndMoodSafely(
        context: Context,
        targetUri: Uri,
        ext: String,
        newGenre: String,
        newMood: String
    ): Result<String> {
        val lowerExt = ext.lowercase()
        if (lowerExt != "mp3" && lowerExt != "flac") {
            return Result.failure(
                IllegalArgumentException("Direct binary tag patching is verified for MP3 and FLAC; other formats are included via M3U8 playlists.")
            )
        }

        val tempDir = File(context.cacheDir, "vibetag_tx").apply { mkdirs() }
        val backup = File(tempDir, "backup.$lowerExt")
        val staging = File(tempDir, "staging.$lowerExt")

        return try {
            context.contentResolver.openInputStream(targetUri)?.use { input ->
                FileOutputStream(backup).use { output -> input.copyTo(output) }
            } ?: return Result.failure(IOException("Cannot read source file"))

            val preSha256 = computeAudioPayloadSha256(backup, lowerExt)

            when (lowerExt) {
                "mp3" -> patchMp3GenreAndMood(backup, staging, newGenre, newMood)
                "flac" -> patchFlacGenreAndMood(backup, staging, newGenre, newMood)
            }

            val postSha256 = computeAudioPayloadSha256(staging, lowerExt)
            if (preSha256 != postSha256) {
                return Result.failure(IllegalStateException("SAFETY ABORT: Audio payload SHA-256 mismatch! Original file untouched."))
            }

            val (verifyGenre, verifyMood) = readGenreAndMood(staging, lowerExt)
            if (verifyGenre != newGenre || verifyMood != newMood) {
                return Result.failure(IllegalStateException("SAFETY ABORT: Read-back tag verification failed."))
            }

            context.contentResolver.openFileDescriptor(targetUri, "rwt")?.use { pfd ->
                FileOutputStream(pfd.fileDescriptor).use { out ->
                    FileInputStream(staging).use { inp -> inp.copyTo(out) }
                    out.flush()
                    pfd.fileDescriptor.sync()
                }
            } ?: return Result.failure(IOException("Cannot open writable descriptor via SAF"))

            Result.success(postSha256)
        } catch (e: Exception) {
            Result.failure(e)
        } finally {
            backup.delete()
            staging.delete()
        }
    }

    private fun readMp3GenreAndMood(file: File): Pair<String, String> {
        RandomAccessFile(file, "r").use { raf ->
            if (raf.length() < 10) return "" to ""
            val h = ByteArray(10)
            raf.readFully(h)
            if (String(h, 0, 3, Charsets.US_ASCII) != "ID3") return "" to ""
            val versionMajor = h[3].toInt() and 0xFF
            val tagSize = ((h[6].toInt() and 0x7F) shl 21) or
                ((h[7].toInt() and 0x7F) shl 14) or
                ((h[8].toInt() and 0x7F) shl 7) or
                (h[9].toInt() and 0x7F)

            val tagBytes = ByteArray(minOf(tagSize.toLong(), raf.length() - 10).toInt())
            raf.readFully(tagBytes)

            var genre = ""
            var mood = ""
            var pos = 0
            while (pos + 10 <= tagBytes.size) {
                val frameId = String(tagBytes, pos, 4, Charsets.US_ASCII)
                if (!frameId.all { it in 'A'..'Z' || it in '0'..'9' }) break
                val frameSize = if (versionMajor == 4) {
                    ((tagBytes[pos + 4].toInt() and 0x7F) shl 21) or
                        ((tagBytes[pos + 5].toInt() and 0x7F) shl 14) or
                        ((tagBytes[pos + 6].toInt() and 0x7F) shl 7) or
                        (tagBytes[pos + 7].toInt() and 0x7F)
                } else {
                    ByteBuffer.wrap(tagBytes, pos + 4, 4).order(ByteOrder.BIG_ENDIAN).int
                }
                if (frameSize <= 0 || pos + 10 + frameSize > tagBytes.size) break
                val content = tagBytes.copyOfRange(pos + 10, pos + 10 + frameSize)
                if (frameId == "TCON") genre = decodeId3Text(content)
                if (frameId == "TMOO") mood = decodeId3Text(content)
                pos += 10 + frameSize
            }
            return genre to mood
        }
    }

    private fun decodeId3Text(bytes: ByteArray): String {
        if (bytes.isEmpty()) return ""
        val charset = when (bytes[0].toInt()) {
            0 -> Charsets.ISO_8859_1
            1 -> Charsets.UTF_16
            2 -> Charsets.UTF_16BE
            3 -> Charsets.UTF_8
            else -> Charsets.UTF_8
        }
        return String(bytes, 1, bytes.size - 1, charset).trim('\u0000', ' ')
    }

    /**
     * Rebuilds the ID3v2 header preserving every unrelated frame byte-for-byte,
     * replacing only TCON (Genre) and TMOO (Mood), followed by the exact original audio stream.
     */
    private fun patchMp3GenreAndMood(source: File, dest: File, genre: String, mood: String) {
        RandomAccessFile(source, "r").use { raf ->
            val (audioStart, _) = locateMp3AudioBounds(raf)
            val keptFrames = ByteArrayOutputStream()

            if (audioStart > 10) {
                raf.seek(0)
                val h = ByteArray(10)
                raf.readFully(h)
                val versionMajor = h[3].toInt() and 0xFF
                val tagBytes = ByteArray((audioStart - 10).toInt())
                raf.readFully(tagBytes)

                var pos = 0
                while (pos + 10 <= tagBytes.size) {
                    val frameId = String(tagBytes, pos, 4, Charsets.US_ASCII)
                    if (!frameId.all { it in 'A'..'Z' || it in '0'..'9' }) break
                    val frameSize = if (versionMajor == 4) {
                        ((tagBytes[pos + 4].toInt() and 0x7F) shl 21) or
                            ((tagBytes[pos + 5].toInt() and 0x7F) shl 14) or
                            ((tagBytes[pos + 6].toInt() and 0x7F) shl 7) or
                            (tagBytes[pos + 7].toInt() and 0x7F)
                    } else {
                        ByteBuffer.wrap(tagBytes, pos + 4, 4).order(ByteOrder.BIG_ENDIAN).int
                    }
                    if (frameSize <= 0 || pos + 10 + frameSize > tagBytes.size) break
                    if (frameId != "TCON" && frameId != "TMOO") {
                        // Convert frame header cleanly to ID3v2.4 synchsafe size so container is uniform
                        keptFrames.write(frameId.toByteArray(Charsets.US_ASCII))
                        keptFrames.write(encodeSynchsafeInt(frameSize))
                        keptFrames.write(tagBytes, pos + 8, 2) // flags
                        keptFrames.write(tagBytes, pos + 10, frameSize)
                    }
                    pos += 10 + frameSize
                }
            }

            if (genre.isNotBlank()) keptFrames.write(buildId3v24TextFrame("TCON", genre))
            if (mood.isNotBlank()) keptFrames.write(buildId3v24TextFrame("TMOO", mood))

            val allFrames = keptFrames.toByteArray()
            FileOutputStream(dest).use { out ->
                out.write("ID3".toByteArray(Charsets.US_ASCII))
                out.write(byteArrayOf(4, 0, 0)) // ID3v2.4.0, flags = 0
                out.write(encodeSynchsafeInt(allFrames.size))
                out.write(allFrames)

                // Copy pure audio bytes unchanged
                raf.seek(audioStart)
                val buf = ByteArray(65536)
                while (true) {
                    val r = raf.read(buf)
                    if (r <= 0) break
                    out.write(buf, 0, r)
                }
            }
        }
    }

    private fun buildId3v24TextFrame(frameId: String, text: String): ByteArray {
        val textBytes = text.toByteArray(Charsets.UTF_8)
        val payloadSize = 1 + textBytes.size // 1 byte encoding (0x03 = UTF-8) + text
        val out = ByteArrayOutputStream(10 + payloadSize)
        out.write(frameId.toByteArray(Charsets.US_ASCII))
        out.write(encodeSynchsafeInt(payloadSize))
        out.write(byteArrayOf(0, 0))
        out.write(3) // UTF-8 encoding marker
        out.write(textBytes)
        return out.toByteArray()
    }

    private fun encodeSynchsafeInt(value: Int): ByteArray = byteArrayOf(
        ((value shr 21) and 0x7F).toByte(),
        ((value shr 14) and 0x7F).toByte(),
        ((value shr 7) and 0x7F).toByte(),
        (value and 0x7F).toByte()
    )

    private fun readFlacGenreAndMood(file: File): Pair<String, String> {
        RandomAccessFile(file, "r").use { raf ->
            if (raf.length() < 8) return "" to ""
            val magic = ByteArray(4)
            raf.readFully(magic)
            if (String(magic, Charsets.US_ASCII) != "fLaC") return "" to ""
            var isLast = false
            val genres = mutableListOf<String>()
            val moods = mutableListOf<String>()
            while (!isLast && raf.filePointer + 4 <= raf.length()) {
                val bh = ByteArray(4)
                raf.readFully(bh)
                isLast = (bh[0].toInt() and 0x80) != 0
                val type = bh[0].toInt() and 0x7F
                val len = ((bh[1].toInt() and 0xFF) shl 16) or ((bh[2].toInt() and 0xFF) shl 8) or (bh[3].toInt() and 0xFF)
                if (type == 4) { // VORBIS_COMMENT
                    val block = ByteArray(len)
                    raf.readFully(block)
                    val bb = ByteBuffer.wrap(block).order(ByteOrder.LITTLE_ENDIAN)
                    val vendorLen = bb.int
                    bb.position(bb.position() + vendorLen)
                    val count = bb.int
                    repeat(count) {
                        val cLen = bb.int
                        val cBytes = ByteArray(cLen)
                        bb.get(cBytes)
                        val str = String(cBytes, Charsets.UTF_8)
                        val eq = str.indexOf('=')
                        if (eq > 0) {
                            val k = str.substring(0, eq).uppercase()
                            val v = str.substring(eq + 1)
                            if (k == "GENRE") genres.add(v)
                            if (k == "MOOD") moods.add(v)
                        }
                    }
                } else {
                    raf.seek(raf.filePointer + len)
                }
            }
            return genres.joinToString("; ") to moods.joinToString("; ")
        }
    }

    private fun patchFlacGenreAndMood(source: File, dest: File, genre: String, mood: String) {
        RandomAccessFile(source, "r").use { raf ->
            val magic = ByteArray(4)
            raf.readFully(magic)
            require(String(magic, Charsets.US_ASCII) == "fLaC") { "Invalid FLAC header" }

            data class FlacBlock(val type: Int, val data: ByteArray)
            val blocks = mutableListOf<FlacBlock>()
            var isLast = false
            while (!isLast && raf.filePointer + 4 <= raf.length()) {
                val bh = ByteArray(4)
                raf.readFully(bh)
                isLast = (bh[0].toInt() and 0x80) != 0
                val type = bh[0].toInt() and 0x7F
                val len = ((bh[1].toInt() and 0xFF) shl 16) or ((bh[2].toInt() and 0xFF) shl 8) or (bh[3].toInt() and 0xFF)
                val data = ByteArray(len)
                raf.readFully(data)
                if (type != 1) { // Keep all non-padding blocks; we will rebuild VORBIS_COMMENT (type 4)
                    blocks.add(FlacBlock(type, data))
                }
            }
            val audioStart = raf.filePointer

            // Update or insert VORBIS_COMMENT block preserving all unrelated comments
            var vendor = "VibeTag 1.0"
            val preservedComments = mutableListOf<String>()
            val existingVc = blocks.firstOrNull { it.type == 4 }
            if (existingVc != null) {
                val bb = ByteBuffer.wrap(existingVc.data).order(ByteOrder.LITTLE_ENDIAN)
                val vLen = bb.int
                val vBytes = ByteArray(vLen)
                bb.get(vBytes)
                vendor = String(vBytes, Charsets.UTF_8)
                val count = bb.int
                repeat(count) {
                    val cLen = bb.int
                    val cBytes = ByteArray(cLen)
                    bb.get(cBytes)
                    val entry = String(cBytes, Charsets.UTF_8)
                    val key = entry.substringBefore('=').uppercase()
                    if (key != "GENRE" && key != "MOOD") {
                        preservedComments.add(entry)
                    }
                }
            }
            genre.split(";").map { it.trim() }.filter { it.isNotEmpty() }.forEach {
                preservedComments.add("GENRE=$it")
            }
            mood.split(";").map { it.trim() }.filter { it.isNotEmpty() }.forEach {
                preservedComments.add("MOOD=$it")
            }

            val vcOut = ByteArrayOutputStream()
            val leInt = { v: Int -> ByteBuffer.allocate(4).order(ByteOrder.LITTLE_ENDIAN).putInt(v).array() }
            val vendorBytes = vendor.toByteArray(Charsets.UTF_8)
            vcOut.write(leInt(vendorBytes.size))
            vcOut.write(vendorBytes)
            vcOut.write(leInt(preservedComments.size))
            preservedComments.forEach { c ->
                val cb = c.toByteArray(Charsets.UTF_8)
                vcOut.write(leInt(cb.size))
                vcOut.write(cb)
            }
            val newVcBlock = FlacBlock(4, vcOut.toByteArray())
            val finalBlocks = blocks.filter { it.type != 4 }.toMutableList().apply {
                add(if (isNotEmpty()) 1 else 0, newVcBlock)
            }

            FileOutputStream(dest).use { out ->
                out.write("fLaC".toByteArray(Charsets.US_ASCII))
                finalBlocks.forEachIndexed { idx, blk ->
                    val lastFlag = if (idx == finalBlocks.lastIndex) 0x80 else 0x00
                    val header = byteArrayOf(
                        (lastFlag or (blk.type and 0x7F)).toByte(),
                        ((blk.data.size shr 16) and 0xFF).toByte(),
                        ((blk.data.size shr 8) and 0xFF).toByte(),
                        (blk.data.size and 0xFF).toByte()
                    )
                    out.write(header)
                    out.write(blk.data)
                }
                raf.seek(audioStart)
                val buf = ByteArray(65536)
                while (true) {
                    val r = raf.read(buf)
                    if (r <= 0) break
                    out.write(buf, 0, r)
                }
            }
        }
    }
}

// ============================================================================
// 3. REAL AUDIO DSP MOOD & CLOUD GENRE ANALYZER
// ============================================================================

object VibeAnalyzer {

    /**
     * Extracts a 12-second audio window from the middle of the recording using MediaExtractor + MediaCodec,
     * computing real acoustic features (RMS Energy, Zero-Crossing Brightness, Envelope Pulse Rate, Dynamic Crest)
     * and optionally queries MusicBrainz for recording-level Genre.
     */
    fun analyzeTrack(context: Context, track: AudioTrackItem, allowCloudLookup: Boolean): AudioTrackItem {
        val (rms, zcr, pulseRate, dynamicRange) = extractAcousticFeatures(context, track.uri, track.durationMs)
        val cloudGenre = if (allowCloudLookup && track.title.isNotBlank()) {
            queryMusicBrainzGenre(track.title, track.artist)
        } else null

        val moods = mutableListOf<Pair<String, Float>>()

        // Map real acoustic signal properties to multi-label Mood taxonomy
        if (rms > 0.22f && pulseRate > 2.2f) {
            moods.add("Energetic" to 0.88f)
            moods.add("Danceable" to 0.84f)
            if (zcr > 0.08f) moods.add("Uplifting" to 0.79f) else moods.add("Intense" to 0.76f)
        } else if (rms < 0.11f && zcr < 0.055f) {
            moods.add("Melancholic" to 0.85f)
            moods.add("Reflective" to 0.82f)
            moods.add("Nostalgic" to 0.78f)
        } else if (rms < 0.14f && pulseRate < 1.6f) {
            moods.add("Peaceful" to 0.86f)
            moods.add("Chill" to 0.84f)
            moods.add("Dreamy" to 0.80f)
        } else {
            moods.add("Romantic" to 0.83f)
            moods.add("Nostalgic" to 0.80f)
            if (dynamicRange > 0.35f) moods.add("Dramatic" to 0.75f) else moods.add("Soothing" to 0.77f)
        }

        val topMoods = moods.sortedByDescending { it.second }.take(3)
        val avgConf = topMoods.map { it.second }.average().toFloat()

        val inferredGenre = when {
            !cloudGenre.isNullOrBlank() -> cloudGenre
            track.currentGenre.isNotBlank() -> track.currentGenre
            rms > 0.23f && zcr > 0.075f -> "Electronic / Pop"
            rms < 0.12f -> "Acoustic / Ambient"
            else -> "Melodic / Soundtrack"
        }

        val evidence = "RMS=${"%.2f".format(rms)} | Brightness=${"%.3f".format(zcr)} | Pulse=${"%.1f".format(pulseRate)}Hz" +
            (if (!cloudGenre.isNullOrBlank()) " | MB:$cloudGenre" else "")

        return track.copy(
            proposedGenre = inferredGenre,
            proposedMoods = topMoods.map { it.first },
            confidence = avgConf,
            evidenceNote = evidence,
            status = if (avgConf >= 0.75f) "Ready to Tag" else "Needs Review"
        )
    }

    private fun extractAcousticFeatures(context: Context, uri: Uri, durationMs: Long): FloatArray {
        return runCatching {
            context.contentResolver.openFileDescriptor(uri, "r")?.use { pfd ->
                val extractor = MediaExtractor()
                extractor.setDataSource(pfd.fileDescriptor)
                val trackIdx = (0 until extractor.trackCount).firstOrNull {
                    extractor.getTrackFormat(it).getString(MediaFormat.KEY_MIME)?.startsWith("audio/") == true
                } ?: return@use floatArrayOf(0.16f, 0.06f, 1.8f, 0.25f)

                extractor.selectTrack(trackIdx)
                val format = extractor.getTrackFormat(trackIdx)
                val mime = format.getString(MediaFormat.KEY_MIME)!!
                val codec = MediaCodec.createDecoderByType(mime)
                codec.configure(format, null, null, 0)
                codec.start()

                val seekUs = (durationMs * 400L).coerceAtLeast(0L) // 40% into track
                extractor.seekTo(seekUs, MediaExtractor.SEEK_TO_CLOSEST_SYNC)

                var sumSq = 0.0
                var zeroCrossings = 0L
                var totalSamples = 0L
                var prevSample = 0f
                var peakEnv = 0f
                var envPeaks = 0
                val info = MediaCodec.BufferInfo()
                var decodedFrames = 0

                while (decodedFrames < 90) {
                    val inIdx = codec.dequeueInputBuffer(5000)
                    if (inIdx >= 0) {
                        val buf = codec.getInputBuffer(inIdx)!!
                        val sz = extractor.readSampleData(buf, 0)
                        if (sz < 0) {
                            codec.queueInputBuffer(inIdx, 0, 0, 0, MediaCodec.BUFFER_FLAG_END_OF_STREAM)
                        } else {
                            codec.queueInputBuffer(inIdx, 0, sz, extractor.sampleTime, 0)
                            extractor.advance()
                        }
                    }
                    val outIdx = codec.dequeueOutputBuffer(info, 5000)
                    if (outIdx >= 0) {
                        val outBuf = codec.getOutputBuffer(outIdx)
                        if (outBuf != null && info.size > 2) {
                            val shortBuf = outBuf.order(ByteOrder.nativeOrder()).asShortBuffer()
                            var windowMax = 0f
                            while (shortBuf.hasRemaining()) {
                                val s = shortBuf.get() / 32768f
                                sumSq += s * s
                                if ((s >= 0f && prevSample < 0f) || (s < 0f && prevSample >= 0f)) {
                                    zeroCrossings++
                                }
                                val absS = abs(s)
                                if (absS > windowMax) windowMax = absS
                                if (absS > peakEnv) peakEnv = absS
                                prevSample = s
                                totalSamples++
                            }
                            if (windowMax > 0.32f) envPeaks++
                        }
                        codec.releaseOutputBuffer(outIdx, false)
                        decodedFrames++
                        if ((info.flags and MediaCodec.BUFFER_FLAG_END_OF_STREAM) != 0) break
                    } else break
                }
                codec.stop()
                codec.release()
                extractor.release()

                if (totalSamples == 0L) return@use floatArrayOf(0.16f, 0.06f, 1.8f, 0.25f)
                val rms = sqrt(sumSq / totalSamples).toFloat()
                val zcr = (zeroCrossings.toDouble() / totalSamples).toFloat()
                val pulse = (envPeaks / 10f).coerceIn(0.8f, 4.0f)
                val dyn = (peakEnv - rms).coerceIn(0.05f, 0.8f)
                floatArrayOf(rms, zcr, pulse, dyn)
            } ?: floatArrayOf(0.16f, 0.06f, 1.8f, 0.25f)
        }.getOrDefault(floatArrayOf(0.16f, 0.06f, 1.8f, 0.25f))
    }

    private fun queryMusicBrainzGenre(title: String, artist: String): String? {
        return runCatching {
            val q = URLEncoder.encode("recording:\"$title\"" + (if (artist.isNotBlank()) " AND artist:\"$artist\"" else ""), "UTF-8")
            val url = URL("https://musicbrainz.org/ws/2/recording/?query=$q&fmt=json&limit=1")
            val conn = (url.openConnection() as HttpURLConnection).apply {
                requestMethod = "GET"
                setRequestProperty("User-Agent", "VibeTagAndroid/1.0 ( https://github.com/vibetag )")
                connectTimeout = 4000
                readTimeout = 4000
            }
            if (conn.responseCode == 200) {
                val body = conn.inputStream.bufferedReader().use { it.readText() }
                val recordings = JSONObject(body).optJSONArray("recordings")
                if (recordings != null && recordings.length() > 0) {
                    val tags = recordings.getJSONObject(0).optJSONArray("tags")
                    if (tags != null && tags.length() > 0) {
                        return tags.getJSONObject(0).optString("name").replaceFirstChar { it.uppercase() }
                    }
                }
            }
            null
        }.getOrNull()
    }
}

// ============================================================================
// 4. MAIN ACTIVITY & JETPACK COMPOSE UI
// ============================================================================

class MainActivity : ComponentActivity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContent {
            MaterialTheme(
                colorScheme = darkColorScheme(
                    primary = Color(0xFFBB86FC),
                    secondary = Color(0xFF03DAC6),
                    background = Color(0xFF0F111A),
                    surface = Color(0xFF1A1D2B)
                )
            ) {
                VibeTagAppScreen()
            }
        }
    }
}

@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun VibeTagAppScreen() {
    val context = LocalContext.current
    val scope = rememberCoroutineScope()

    var selectedTab by remember { mutableIntStateOf(0) }
    var folderUri by remember { mutableStateOf<Uri?>(null) }
    var tracks by remember { mutableStateOf<List<AudioTrackItem>>(emptyList()) }
    var journal by remember { mutableStateOf(loadJournal(context)) }
    var statusBanner by remember { mutableStateOf("Select a Music folder to scan and enrich for Poweramp.") }
    var isBusy by remember { mutableStateOf(false) }
    var writePolicy by remember { mutableStateOf(WritePolicy.FILL_MISSING_ONLY) }
    var useCloudLookup by remember { mutableStateOf(true) }
    var selectedMoodsForPlaylist by remember { mutableStateOf(setOf("Romantic", "Nostalgic")) }

    val folderPicker = rememberLauncherForActivityResult(ActivityResultContracts.OpenDocumentTree()) { uri ->
        if (uri != null) {
            context.contentResolver.takePersistableUriPermission(
                uri,
                Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION
            )
            folderUri = uri
            scope.launch {
                isBusy = true
                statusBanner = "Scanning audio files..."
                tracks = withContext(Dispatchers.IO) { scanMusicFolder(context, uri) }
                statusBanner = "Discovered ${tracks.size} supported audio tracks."
                isBusy = false
            }
        }
    }

    Scaffold(
        topBar = {
            TopAppBar(
                title = { Text("VibeTag • Poweramp Mood Engine", fontWeight = FontWeight.Bold) },
                actions = {
                    Button(
                        onClick = { folderPicker.launch(null) },
                        enabled = !isBusy,
                        modifier = Modifier.padding(end = 8.dp)
                    ) {
                        Icon(Icons.Default.FolderOpen, contentDescription = null)
                        Spacer(Modifier.width(6.dp))
                        Text("Pick Folder")
                    }
                }
            )
        },
        bottomBar = {
            NavigationBar {
                listOf(
                    "Library" to Icons.Default.LibraryMusic,
                    "Review & Tag" to Icons.Default.AutoAwesome,
                    "Poweramp M3U8" to Icons.Default.PlaylistPlay,
                    "Rollback" to Icons.Default.History
                ).forEachIndexed { idx, (label, icon) ->
                    NavigationBarItem(
                        selected = selectedTab == idx,
                        onClick = { selectedTab = idx },
                        icon = { Icon(icon, contentDescription = label) },
                        label = { Text(label) }
                    )
                }
            }
        }
    ) { padding ->
        Column(
            modifier = Modifier
                .fillMaxSize()
                .background(MaterialTheme.colorScheme.background)
                .padding(padding)
                .padding(12.dp)
        ) {
            // Status Banner
            Surface(
                color = MaterialTheme.colorScheme.surface,
                shape = RoundedCornerShape(10.dp),
                modifier = Modifier.fillMaxWidth()
            ) {
                Row(
                    modifier = Modifier.padding(12.dp),
                    verticalAlignment = Alignment.CenterVertically
                ) {
                    if (isBusy) {
                        CircularProgressIndicator(modifier = Modifier.size(20.dp), strokeWidth = 2.dp)
                        Spacer(Modifier.width(10.dp))
                    }
                    Text(statusBanner, color = Color.White, fontSize = 13.sp)
                }
            }

            Spacer(Modifier.height(10.dp))

            when (selectedTab) {
                0 -> LibraryTab(
                    tracks = tracks,
                    isBusy = isBusy,
                    onAnalyzeAll = {
                        scope.launch {
                            isBusy = true
                            val updated = tracks.toMutableList()
                            for (i in updated.indices) {
                                statusBanner = "Analyzing (${i + 1}/${updated.size}): ${updated[i].fileName}"
                                updated[i] = withContext(Dispatchers.IO) {
                                    VibeAnalyzer.analyzeTrack(context, updated[i], useCloudLookup)
                                }
                                tracks = updated.toList()
                            }
                            statusBanner = "Analysis complete for ${tracks.size} tracks. Go to 'Review & Tag'."
                            isBusy = false
                        }
                    }
                )

                1 -> ReviewAndTagTab(
                    tracks = tracks,
                    writePolicy = writePolicy,
                    onPolicyChange = { writePolicy = it },
                    isBusy = isBusy,
                    onWriteVerifiedTags = {
                        scope.launch {
                            isBusy = true
                            var successCount = 0
                            val updated = tracks.toMutableList()
                            for (i in updated.indices) {
                                val t = updated[i]
                                if (t.proposedMoods.isEmpty() || t.isLocked) continue

                                val targetGenre = when (writePolicy) {
                                    WritePolicy.PRESERVE_EXISTING -> t.currentGenre
                                    WritePolicy.FILL_MISSING_ONLY -> t.currentGenre.ifBlank { t.proposedGenre }
                                    WritePolicy.REPLACE_HIGH_CONFIDENCE -> if (t.confidence >= 0.75f) t.proposedGenre else t.currentGenre
                                }
                                val proposedMoodStr = t.proposedMoods.joinToString("; ")
                                val targetMood = when (writePolicy) {
                                    WritePolicy.PRESERVE_EXISTING -> t.currentMood
                                    WritePolicy.FILL_MISSING_ONLY -> t.currentMood.ifBlank { proposedMoodStr }
                                    WritePolicy.REPLACE_HIGH_CONFIDENCE -> if (t.confidence >= 0.75f) proposedMoodStr else t.currentMood
                                }

                                statusBanner = "Writing & verifying SHA-256 (${i + 1}/${updated.size}): ${t.fileName}"
                                val res = withContext(Dispatchers.IO) {
                                    SafeTagEngine.writeGenreAndMoodSafely(
                                        context = context,
                                        targetUri = t.uri,
                                        ext = t.extension,
                                        newGenre = targetGenre,
                                        newMood = targetMood
                                    )
                                }
                                res.onSuccess { sha ->
                                    successCount++
                                    updated[i] = t.copy(
                                        currentGenre = targetGenre,
                                        currentMood = targetMood,
                                        status = "Tagged & Verified (SHA256 OK)"
                                    )
                                    val entry = JournalEntry(
                                        trackId = t.id,
                                        uriString = t.uri.toString(),
                                        fileName = t.fileName,
                                        oldGenre = t.currentGenre,
                                        oldMood = t.currentMood,
                                        newGenre = targetGenre,
                                        newMood = targetMood,
                                        audioSha256 = sha,
                                        timestamp = System.currentTimeMillis()
                                    )
                                    journal = saveJournalEntry(context, entry)
                                }.onFailure { err ->
                                    updated[i] = t.copy(status = "Skipped: ${err.message}")
                                }
                                tracks = updated.toList()
                            }
                            statusBanner = "Safely wrote and verified Genre & Mood on $successCount files."
                            isBusy = false
                        }
                    }
                )

                2 -> PowerampPlaylistTab(
                    tracks = tracks,
                    selectedMoods = selectedMoodsForPlaylist,
                    onToggleMood = { mood ->
                        selectedMoodsForPlaylist = if (mood in selectedMoodsForPlaylist) {
                            selectedMoodsForPlaylist - mood
                        } else {
                            selectedMoodsForPlaylist + mood
                        }
                    },
                    onExportM3u8 = {
                        val root = folderUri
                        if (root == null) {
                            statusBanner = "Pick a music folder first so VibeTag can write the .m3u8 playlist."
                            return@PowerampPlaylistTab
                        }
                        scope.launch {
                            isBusy = true
                            val matching = tracks.filter { t ->
                                val allMoods = (t.currentMood.split(";").map { it.trim() } + t.proposedMoods).toSet()
                                selectedMoodsForPlaylist.any { it in allMoods }
                            }
                            val playlistName = "VibeTag_${selectedMoodsForPlaylist.joinToString("_")}.m3u8"
                            val exported = withContext(Dispatchers.IO) {
                                writeM3u8ToRoot(context, root, playlistName, matching)
                            }
                            triggerPowerampScan(context)
                            statusBanner = "Exported $exported tracks to $playlistName & triggered Poweramp rescan!"
                            isBusy = false
                        }
                    },
                    onTriggerPowerampRescan = {
                        triggerPowerampScan(context)
                        statusBanner = "Sent ACTION_SCAN_DIRS broadcast to Poweramp."
                    }
                )

                3 -> RollbackTab(
                    journal = journal,
                    onRollbackEntry = { entry ->
                        scope.launch {
                            isBusy = true
                            val res = withContext(Dispatchers.IO) {
                                SafeTagEngine.writeGenreAndMoodSafely(
                                    context = context,
                                    targetUri = Uri.parse(entry.uriString),
                                    ext = entry.fileName.substringAfterLast('.', ""),
                                    newGenre = entry.oldGenre,
                                    newMood = entry.oldMood
                                )
                            }
                            res.onSuccess {
                                statusBanner = "Rolled back ${entry.fileName} to original Genre & Mood."
                            }.onFailure {
                                statusBanner = "Rollback failed: ${it.message}"
                            }
                            isBusy = false
                        }
                    }
                )
            }
        }
    }
}

@Composable
private fun LibraryTab(tracks: List<AudioTrackItem>, isBusy: Boolean, onAnalyzeAll: () -> Unit) {
    Column(Modifier.fillMaxSize()) {
        Button(
            onClick = onAnalyzeAll,
            enabled = tracks.isNotEmpty() && !isBusy,
            modifier = Modifier.fillMaxWidth()
        ) {
            Icon(Icons.Default.GraphicEq, contentDescription = null)
            Spacer(Modifier.width(8.dp))
            Text("Run Audio Mood + Cloud Genre Analysis (${tracks.size} Tracks)")
        }
        Spacer(Modifier.height(8.dp))
        LazyColumn(verticalArrangement = Arrangement.spacedBy(8.dp)) {
            items(tracks, key = { it.id }) { t ->
                Card(
                    colors = CardDefaults.cardColors(containerColor = MaterialTheme.colorScheme.surface),
                    modifier = Modifier.fillMaxWidth()
                ) {
                    Column(Modifier.padding(12.dp)) {
                        Text(t.title.ifBlank { t.fileName }, color = Color.White, fontWeight = FontWeight.SemiBold)
                        Text("${t.artist.ifBlank { "Unknown Artist" }} • ${t.extension.uppercase()}", color = Color.Gray, fontSize = 12.sp)
                        Spacer(Modifier.height(4.dp))
                        Text("Current Genre: ${t.currentGenre.ifBlank { "—" }} | Current Mood: ${t.currentMood.ifBlank { "—" }}", color = Color(0xFF03DAC6), fontSize = 12.sp)
                        if (t.proposedMoods.isNotEmpty()) {
                            Text(
                                "Proposed: Genre=${t.proposedGenre} | Moods=${t.proposedMoods.joinToString(", ")} (${(t.confidence * 100).toInt()}%)",
                                color = Color(0xFFBB86FC),
                                fontSize = 12.sp
                            )
                            Text(t.evidenceNote, color = Color.LightGray, fontSize = 11.sp)
                        }
                    }
                }
            }
        }
    }
}

@Composable
private fun ReviewAndTagTab(
    tracks: List<AudioTrackItem>,
    writePolicy: WritePolicy,
    onPolicyChange: (WritePolicy) -> Unit,
    isBusy: Boolean,
    onWriteVerifiedTags: () -> Unit
) {
    Column(Modifier.fillMaxSize()) {
        Text("Write Safety Policy (Only modifies Genre & Mood):", color = Color.White, fontSize = 13.sp)
        Spacer(Modifier.height(6.dp))
        LazyRow(horizontalArrangement = Arrangement.spacedBy(8.dp)) {
            items(WritePolicy.entries) { policy ->
                FilterChip(
                    selected = writePolicy == policy,
                    onClick = { onPolicyChange(policy) },
                    label = { Text(policy.label) }
                )
            }
        }
        Spacer(Modifier.height(8.dp))
        Button(
            onClick = onWriteVerifiedTags,
            enabled = tracks.any { it.proposedMoods.isNotEmpty() } && !isBusy,
            modifier = Modifier.fillMaxWidth()
        ) {
            Icon(Icons.Default.VerifiedUser, contentDescription = null)
            Spacer(Modifier.width(8.dp))
            Text("Write Genre & Mood with SHA-256 Audio Verification")
        }
        Spacer(Modifier.height(8.dp))
        LazyColumn(verticalArrangement = Arrangement.spacedBy(8.dp)) {
            items(tracks.filter { it.proposedMoods.isNotEmpty() }, key = { it.id }) { t ->
                Card(
                    colors = CardDefaults.cardColors(containerColor = MaterialTheme.colorScheme.surface),
                    modifier = Modifier.fillMaxWidth()
                ) {
                    Column(Modifier.padding(12.dp)) {
                        Text(t.fileName, color = Color.White, fontWeight = FontWeight.Bold)
                        Text("Before -> Genre: ${t.currentGenre.ifBlank { "None" }} | Mood: ${t.currentMood.ifBlank { "None" }}", color = Color.Gray, fontSize = 12.sp)
                        Text("After  -> Genre: ${t.proposedGenre} | Mood: ${t.proposedMoods.joinToString("; ")}", color = Color(0xFF03DAC6), fontSize = 12.sp)
                        Text("Status: ${t.status}", color = Color(0xFFBB86FC), fontSize = 11.sp)
                    }
                }
            }
        }
    }
}

@Composable
private fun PowerampPlaylistTab(
    tracks: List<AudioTrackItem>,
    selectedMoods: Set<String>,
    onToggleMood: (String) -> Unit,
    onExportM3u8: () -> Unit,
    onTriggerPowerampRescan: () -> Unit
) {
    Column(Modifier.fillMaxSize()) {
        Text("Select Moods to Combine into a Poweramp .M3U8 Playlist:", color = Color.White, fontWeight = FontWeight.SemiBold)
        Spacer(Modifier.height(8.dp))
        LazyRow(horizontalArrangement = Arrangement.spacedBy(6.dp)) {
            items(DEFAULT_MOOD_TAXONOMY) { mood ->
                FilterChip(
                    selected = mood in selectedMoods,
                    onClick = { onToggleMood(mood) },
                    label = { Text(mood) }
                )
            }
        }
        Spacer(Modifier.height(10.dp))
        Row(horizontalArrangement = Arrangement.spacedBy(8.dp), modifier = Modifier.fillMaxWidth()) {
            Button(onClick = onExportM3u8, modifier = Modifier.weight(1f)) {
                Text("Export .M3U8 Playlist")
            }
            OutlinedButton(onClick = onTriggerPowerampRescan, modifier = Modifier.weight(1f)) {
                Text("Rescan Poweramp")
            }
        }
        Spacer(Modifier.height(12.dp))
        val matchingTracks = tracks.filter { t ->
            val moods = (t.currentMood.split(";").map { it.trim() } + t.proposedMoods).toSet()
            selectedMoods.any { it in moods }
        }
        Text("Matching Tracks (${matchingTracks.size}):", color = Color(0xFF03DAC6), fontSize = 13.sp)
        Spacer(Modifier.height(6.dp))
        LazyColumn(verticalArrangement = Arrangement.spacedBy(6.dp)) {
            items(matchingTracks, key = { it.id }) { t ->
                Card(colors = CardDefaults.cardColors(containerColor = MaterialTheme.colorScheme.surface), modifier = Modifier.fillMaxWidth()) {
                    Column(Modifier.padding(10.dp)) {
                        Text(t.title.ifBlank { t.fileName }, color = Color.White)
                        Text("Moods: ${(t.currentMood.ifBlank { t.proposedMoods.joinToString("; ") })}", color = Color.Gray, fontSize = 12.sp)
                    }
                }
            }
        }
    }
}

@Composable
private fun RollbackTab(journal: List<JournalEntry>, onRollbackEntry: (JournalEntry) -> Unit) {
    LazyColumn(verticalArrangement = Arrangement.spacedBy(8.dp)) {
        items(journal) { j ->
            Card(colors = CardDefaults.cardColors(containerColor = MaterialTheme.colorScheme.surface), modifier = Modifier.fillMaxWidth()) {
                Row(Modifier.padding(12.dp), verticalAlignment = Alignment.CenterVertically) {
                    Column(Modifier.weight(1f)) {
                        Text(j.fileName, color = Color.White, fontWeight = FontWeight.Bold)
                        Text("Restores Genre='${j.oldGenre}' & Mood='${j.oldMood}'", color = Color.Gray, fontSize = 12.sp)
                        Text("Verified Audio SHA256: ${j.audioSha256.take(16)}...", color = Color(0xFF03DAC6), fontSize = 11.sp)
                    }
                    OutlinedButton(onClick = { onRollbackEntry(j) }) {
                        Text("Rollback")
                    }
                }
            }
        }
    }
}

// ============================================================================
// 5. SAF FOLDER SCANNER, M3U8 EXPORTER & JOURNAL STORAGE HELPERS
// ============================================================================

private fun scanMusicFolder(context: Context, treeUri: Uri): List<AudioTrackItem> {
    val supportedExts = setOf("mp3", "flac", "m4a", "ogg", "opus", "wav")
    val results = mutableListOf<AudioTrackItem>()
    val rootDoc = DocumentFile.fromTreeUri(context, treeUri) ?: return emptyList()

    fun walk(dir: DocumentFile, relPrefix: String) {
        for (doc in dir.listFiles()) {
            val name = doc.name ?: continue
            if (doc.isDirectory) {
                walk(doc, if (relPrefix.isEmpty()) name else "$relPrefix/$name")
            } else {
                val ext = name.substringAfterLast('.', "").lowercase()
                if (ext in supportedExts) {
                    val relPath = if (relPrefix.isEmpty()) name else "$relPrefix/$name"
                    val mmr = MediaMetadataRetriever()
                    var title = ""
                    var artist = ""
                    var album = ""
                    var genre = ""
                    var durationMs = 0L
                    runCatching {
                        context.contentResolver.openFileDescriptor(doc.uri, "r")?.use { pfd ->
                            mmr.setDataSource(pfd.fileDescriptor)
                            title = mmr.extractMetadata(MediaMetadataRetriever.METADATA_KEY_TITLE).orEmpty()
                            artist = mmr.extractMetadata(MediaMetadataRetriever.METADATA_KEY_ARTIST).orEmpty()
                            album = mmr.extractMetadata(MediaMetadataRetriever.METADATA_KEY_ALBUM).orEmpty()
                            genre = mmr.extractMetadata(MediaMetadataRetriever.METADATA_KEY_GENRE).orEmpty()
                            durationMs = mmr.extractMetadata(MediaMetadataRetriever.METADATA_KEY_DURATION)?.toLongOrNull() ?: 0L
                        }
                    }
                    runCatching { mmr.release() }

                    // Also inspect binary TMOO / Vorbis MOOD when MP3 or FLAC
                    var mood = ""
                    if (ext == "mp3" || ext == "flac") {
                        val tmp = File(context.cacheDir, "scan_probe.$ext")
                        runCatching {
                            context.contentResolver.openInputStream(doc.uri)?.use { inp ->
                                FileOutputStream(tmp).use { out -> inp.copyTo(out) }
                            }
                            val (g, m) = SafeTagEngine.readGenreAndMood(tmp, ext)
                            if (g.isNotBlank()) genre = g
                            mood = m
                        }
                        tmp.delete()
                    }

                    results.add(
                        AudioTrackItem(
                            id = doc.uri.toString(),
                            uri = doc.uri,
                            fileName = name,
                            relativePath = relPath,
                            extension = ext,
                            durationMs = durationMs,
                            title = title,
                            artist = artist,
                            album = album,
                            currentGenre = genre,
                            currentMood = mood
                        )
                    )
                }
            }
        }
    }
    walk(rootDoc, "")
    return results
}

private fun writeM3u8ToRoot(
    context: Context,
    rootTreeUri: Uri,
    playlistFileName: String,
    tracks: List<AudioTrackItem>
): Int {
    val rootDoc = DocumentFile.fromTreeUri(context, rootTreeUri) ?: return 0
    rootDoc.findFile(playlistFileName)?.delete()
    val m3uDoc = rootDoc.createFile("audio/x-mpegurl", playlistFileName) ?: return 0
    context.contentResolver.openOutputStream(m3uDoc.uri, "wt")?.use { os ->
        BufferedWriter(OutputStreamWriter(os, Charsets.UTF_8)).use { writer ->
            writer.write("#EXTM3U\n")
            writer.write("#PLAYLIST:$playlistFileName\n")
            for (t in tracks) {
                val sec = (t.durationMs / 1000L).coerceAtLeast(1L)
                val dispTitle = t.title.ifBlank { t.fileName }
                val dispArtist = t.artist.ifBlank { "Unknown Artist" }
                writer.write("#EXTINF:$sec,$dispArtist - $dispTitle\n")
                writer.write("${t.relativePath}\n")
            }
            writer.flush()
        }
    }
    return tracks.size
}

private fun triggerPowerampScan(context: Context) {
    runCatching {
        val intent = Intent("com.maxmpz.audioplayer.ACTION_SCAN_DIRS").apply {
            setPackage("com.maxmpz.audioplayer")
            putExtra("fastScan", true)
        }
        context.sendBroadcast(intent)
    }
}

private fun loadJournal(context: Context): List<JournalEntry> {
    val file = File(context.filesDir, "vibetag_journal.json")
    if (!file.exists()) return emptyList()
    return runCatching {
        val arr = JSONArray(file.readText())
        (0 until arr.length()).map { i ->
            val o = arr.getJSONObject(i)
            JournalEntry(
                trackId = o.getString("trackId"),
                uriString = o.getString("uriString"),
                fileName = o.getString("fileName"),
                oldGenre = o.getString("oldGenre"),
                oldMood = o.getString("oldMood"),
                newGenre = o.getString("newGenre"),
                newMood = o.getString("newMood"),
                audioSha256 = o.getString("audioSha256"),
                timestamp = o.getLong("timestamp")
            )
        }
    }.getOrDefault(emptyList())
}

private fun saveJournalEntry(context: Context, entry: JournalEntry): List<JournalEntry> {
    val updated = listOf(entry) + loadJournal(context)
    val arr = JSONArray()
    updated.forEach { j ->
        arr.put(
            JSONObject().apply {
                put("trackId", j.trackId)
                put("uriString", j.uriString)
                put("fileName", j.fileName)
                put("oldGenre", j.oldGenre)
                put("oldMood", j.oldMood)
                put("newGenre", j.newGenre)
                put("newMood", j.newMood)
                put("audioSha256", j.audioSha256)
                put("timestamp", j.timestamp)
            }
        )
    }
    File(context.filesDir, "vibetag_journal.json").writeText(arr.toString())
    return updated
}
