# slang_video_live_spec times out: 413 example is O(payload) in the seed interpreter

Date: 2026-11-24. Spec: `test/03_system/lib/slang/feature/slang_video_live_spec.spl`.
Class: performance (not a functional failure). Seed: `C:/dev/seeds/simple-release.exe`, Radeon 8065S, Vulkan ggml shim built from release tip.

## Symptom
`SPEC FILE VERDICT ... timeout=1 reason=child-timeout budget_ms=900000` (also
`budget_ms=1700000` with `test --timeout 1700`). Logs:
`C:/dev/slang-logs/sweep/media/{video,video_r2,video_long,video_fix}.log`.

## Where the time goes
- Example 1 (mp4 -> SmolVLM2 on GPU) PASSES and is not the stall: `VIDEO-ANSWER total_ms` 113433 / 145186 / 284183 across runs (status 200, sensible answer), `FRAME-EXTRACT` 0.5-2.8 s.
- Example 2 ("413 for a video over 10 MiB") never finishes. The spec builds a 10 MiB `[u8]` with a push loop and `base64_encode_bytes` it, then `serve_chat_completions` parses a ~14 MB JSON body and base64-decodes it, all interpreted. Measured in spec context (interpreter):
  - encode: 100k bytes 5.4 s, 400k 21.4 s, 1M 56.6 s (~54 us/byte, linear; push loop ~5 us/byte)
  - decode: 196 608 bytes 7.3 s (~37 us/byte)
  - `serve_chat_completions` request parse before any size check: 64 KiB chars 2.7 s, 256 KiB 11.9 s, 1 MiB 46.3 s (~44 us/char, linear)
  - extrapolated for the 10 MiB case: encode ~570 s + parse of ~14 MB body ~600 s + decode ~390 s, i.e. well over 1500 s.
- A longer budget does NOT make it pass at 1700 s. The same code under a compiled binary is expected to be orders of magnitude faster (JIT `main` probe: 1.6M-byte encode 53 ms), so this is a seed-interpreter cost, not a product defect.

## Things tried
Replacing the 10 MiB array with a doubled `"AAAA"` string and adding an encoded-length precheck before decode still timed out (`video_fix.log`), because request JSON parsing dominates. Reverted; not worth carrying.

## Options (owner decision)
1. Move the 413 example to a unit spec that calls a size-check helper directly (needs the helper extracted from `serving_chat`).
2. Make `video_max_bytes()` overridable for tests so a small payload exercises the 413 path.
3. Keep as is and run it only under a compiled binary.
