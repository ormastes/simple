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
- Build logs:
  `build/simpleos_gpu_host/offload_policy/native-build.out` and
  `native-build-cycle2.out`.

No bootstrap was run. The policy source, protocol reason, tests, and manuals
retain only the verified small-request bypass claim. Three focused native
build/run cycles are exhausted. A source-matched pure-Simple compiler plus the
complete-provider runtime archive subsequently rebuilt and verified the current
daemon without bootstrap.

## Remaining Gate

Run a batch at or above `1,048,576` without fault injection to retain an exact
successful device-path receipt. Strict fallback `none` remains covered by the
executable source contract until then.

Owner: Linux GPU host operator. Final reviewer: high-capability model.
