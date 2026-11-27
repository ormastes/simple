# slang whisper: ~30 s per request for an 11 s clip, dominated by wav decode in Simple

Measured 2026-11-18 on the Rust seed (`bin/simple.exe`), `whisper-tiny.en`, `jfk.wav`
(176,000 samples, 16 kHz mono): `serve_transcriptions` takes 32.0 s, then 30.1 s on a
second call with the model already resident. whisper.cpp itself transcribes this clip in
about a second, so the cost is `wav_to_pcm16` (`decode_wav` pushing 176k f32 samples, then
a second per-sample loop pushing 352k bytes) running in the interpreter.

Fix direction: for a PCM16 mono 16 kHz wav hand the data chunk to the shim as bytes
without the f32 round trip (a `with_bytes` offset/length over the original file), or add a
packed decode in the stdlib; both are L2-style byte plumbing.
