# SimpleOS GPU Offload Policy Native CLI Segfault

## Status

Resolved for policy admission and calibrated small-batch bypass. Linux CUDA
measurement now drives a default `1,048,576`-element threshold; CPU fallback
requests below it publish reason `18` before device execution. Native
threshold-`0` CUDA submit fallback now completes with reason `16`.

## Evidence

- Retained break-even: CPU at 64 and 65,536 elements; CUDA at 1,048,576 and
  8,388,608; median communication overhead 1,832 us.
- Focused policy contract reached `7 examples, 0 failures` with the Rust seed.
  This is source-contract evidence, not native daemon admission.
- First incremental native build: `212 compiled, 0 failed`; method parsing
  retained unresolved `str.parse_i64`.
- Replacing method parsing with `std.common.text.parse_i64` rebuilt
  incrementally: `2 compiled, 211 cached, 0 failed` and removed that unresolved
  symbol.
- The resulting
  `build/simpleos_gpu_host/offload_policy/simpleos_gpu_host` exited `139` for
  `--processing-min-offload-elements=bad` before printing validation output.
- After the shared mmap native-ABI repair, the incrementally rebuilt current
  daemon now reaches existing CLI validation and exits `2` with the expected
  invalid-processing-backend diagnostic.
- The reapplied option uses canonical integer round-trip validation; malformed
  input exits `2` with the expected threshold diagnostic.
- Policy source contract passes 8/8.
- Native 8-element calibrated request passes with fallback status `4`, reason
  `18`, CPU source `2`, zero handle/identity, 32 bytes, and exact checksum.
- Threshold `0` enters CUDA and completes the injected-submit fallback with
  reason `16`, CPU source `2`, zero handle/identity, and the exact checksum.
- The retained direct ProcessingIR candidate now completes exactly at the
  calibrated `1,048,576`-element threshold with checksum `17730434498560`,
  zero mismatches, positive handle/identity, device readback, and no fallback.
- Reusing the runtime-owned `rt_u32s_from_raw` readback converter removed the
  executor's million-call `values.push` loop and reduced measured cold
  execution from `1044501 us` to `593323 us`.
- Reusing one process-owned CUDA context/module completed the exact
  1,048,576-element request in `861499 us` cold and `69331 us` warm (12.4x
  faster) with the same positive device provenance and no fallback.
- Build logs:
  `build/simpleos_gpu_host/offload_policy/native-build.out` and
  `native-build-cycle2.out`.

No bootstrap was run. The policy source, protocol reason, tests, and manuals
retain only the verified small-request bypass claim. Three focused native
build/run cycles are exhausted. A source-matched pure-Simple compiler plus the
complete-provider runtime archive subsequently rebuilt and verified the current
daemon without bootstrap.

The retained-session daemon-wire continuation added a strict probe for three
warmups plus five measured exact 1,048,576-element CUDA requests. The probe
build passes with `1 compiled, 18 cached, 0 failed`, no generated stubs, and a
passing median self-test. A refreshed CUDA/Vulkan runtime archive and strict
daemon link pass with `2 compiled, 215 cached, 0 failed`, but the first live
device-warm attempt crashed before transport readiness. Read-only object
relocation inspection found a self-recursive `str_starts_with` pulled in by a
new `common.string_core` dependency in byte decoding. The final source removes
that dependency and calls `rt_char_from_code` directly. The three daemon build
cycles are exhausted, so that final source state remains unbuilt and no new
device-wire timing is claimed.

## Remaining Gate

Publish the same at-threshold success through the daemon wire. The current
direct receipt closes executor correctness, but not the daemon client path or
its independent CPU-oracle comparison. Then retain the required warm
multi-sample medians; the single direct warm receipt does not justify the
lower-level CUDA round-trip threshold by itself. Resume with one strict
incremental daemon build from the retained cache, then run
`SIMPLEOS_GPU_FALLBACK_WIRE_MODE=device-warm sh
scripts/check/check-simpleos-gpu-fallback-wire.shs`.

Owner: Linux GPU host operator. Final reviewer: high-capability model.
