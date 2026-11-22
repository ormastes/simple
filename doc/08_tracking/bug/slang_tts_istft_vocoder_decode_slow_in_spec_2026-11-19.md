# slang TTS: ISTFT and vocoder f32 decode are ~18x slower inside the live spec than under `run`

Status: open perf defect, recorded per CLAUDE.md (meaningful perf regression found
during verification). Cause not isolated.

## Evidence (Windows, release seed `C:/dev/seeds/simple-release.exe`, CPU mtmd shim)

`test/03_system/lib/slang/feature/slang_tts_live_spec.spl`, per-stage timings from
`tts_runner.tts_last_timings()` (logs under `C:/dev/slang-logs/l5/`):

| run | frames (codes) | vocoder_ms | istft_wav_ms | per frame |
|---|---|---|---|---|
| run1 (2048-token cap) | 1000 | 172979 | 745501 | ~745 ms |
| run2 top-k | 159 | 38026 | 123086 | ~774 ms |
| run3 greedy | 153 | 29494 | 116978 | ~765 ms |

The same `istft.embd_to_audio` under `simple-release.exe run build/probe/istft_perf.spl`
(synthetic rows, same 1282-wide geometry):

| frames | ms | per frame |
|---|---|---|
| 20 | 503 | 25 ms |
| 100 | 3774 | 38 ms |
| 200 | 8393 | 42 ms |
| 400 | 17877 | 45 ms |
| 1000 | 50463 | 50 ms |

16-bit wav encode + base64 of 50880 samples under `run`: 4 ms + 1 ms, so the
`istft_wav_ms` span is the ISTFT. Ruled out: indexed writes into large arrays
(1000 writes into a 320k array: 0 ms), array reads (100k reads: 6-26 ms), and the
in-place 0.25 s zeroing (replaced by a one-pass build; run2 per-frame time
unchanged). A 1.2M-element live ballast slows the `run` probe by only 1.5x.

`vocoder_ms` includes `backend.f32_le_to_floats` over n_codes x 1282 floats
(~200k for run2), decoded per element in interpreted code (design doc
`slang_pluggable_modalities.md` gap G9).

## Next step

Time `embd_to_audio` inside a `simple test` spec on the same synthetic rows to
confirm whether the slowdown is the test-runner execution mode, then profile.
