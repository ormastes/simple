<!-- codex-research -->
# Sound Engine Domain Research

## Platform Device Backend
miniaudio is already vendored in this repo and is a strong fit for the lightweight native bridge. Its project documentation lists Windows, macOS, iOS, Linux, FreeBSD/OpenBSD/NetBSD, Android, Raspberry Pi, and Emscripten/HTML5 as supported platforms, and notes that unsupported platforms can use custom backends without modifying miniaudio. Sources: https://miniaud.io/ and https://github.com/mackron/miniaudio

Implication for Simple: keep miniaudio at the runtime boundary for host OS device I/O, but expose Simple-owned capability status and avoid treating `rt_audio_init() == 0` as an unstructured failure.

## Codecs
Opus is standardized by IETF RFC 6716 for interactive speech and audio and spans low-bitrate speech through high-quality stereo music. The Opus project describes it as open, royalty-free, versatile, and suitable for storage and streaming as well as interactive use. Sources: https://datatracker.ietf.org/doc/html/rfc6716 and https://opus-codec.org/

Vorbis is an open, royalty-free, general-purpose compressed audio format for mid-to-high quality music and sound assets. Xiph documents Ogg Vorbis as suitable for fixed and variable bitrates and broad audio/music use. Source: https://xiph.org/vorbis/

Implication for Simple: a pure-Simple first milestone should probably avoid promising a complete Opus/Vorbis encoder immediately. A safer path is a Simple-owned lossless/PCM container plus optional future Opus/Vorbis-compatible decode or import tooling, with fixed vectors and corrupt-input rejection from day one.

## Security And Hardening
RFC 8251 records security fixes to the Opus codec specification/reference behavior, including CVE-linked decoder issues. Source: https://www.rfc-editor.org/rfc/rfc8251.html

Implication for Simple: codec work must include malformed packet rejection, bounded allocation, frame-size validation, and fuzz-style edge cases before it can be called hardened.

## Real-Time And Parallel Audio
Game audio engines usually separate real-time mixer deadlines from slower asset preparation and streaming decode. The critical design concern is deterministic bounded work at the mixer boundary: background workers may decode, resample, or prepare buffers, but audio callback/mixer state must avoid blocking, unbounded allocation, and nondeterministic ordering.

Implication for Simple: use parallel tasks for asset prep and streaming decode, then hand the mixer deterministic ready buffers/commands. Inline fallback must be explicit when worker-pool runtime support is unavailable.

## Spatial Audio
The existing miniaudio-backed API already supports sound position, listener position/direction/up, distance bounds, and pitch. For game development, the missing domain layer is not raw 3D calls but stable binding between scene transforms and audio commands, plus deterministic tests for attenuation/Doppler/occlusion metadata.

## Recommended Domain Position
- Device I/O: miniaudio native bridge plus Simple capability facade.
- First codec: Simple lossless/PCM or ADPCM-like game asset codec before full Opus/Vorbis.
- High-quality target: design for Opus/Vorbis import/decode compatibility later, but do not block the first engine on a full pure-Simple Opus encoder.
- Parallelism: background decode/asset-prep jobs, deterministic mixer queue.
- Hardening: codec parser and backend lifecycle tests are first-class release gates.
