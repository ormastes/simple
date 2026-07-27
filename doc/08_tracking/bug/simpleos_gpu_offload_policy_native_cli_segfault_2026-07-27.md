# SimpleOS GPU Offload Policy Native CLI Segfault

## Status

Open. Linux CUDA measurement proves CPU is faster below 1,048,576 ProcessingIR
elements, but `src/app/simpleos_gpu_host/main.spl` still executes both the CPU
oracle and requested GPU backend for every valid processing request. A
calibrated pre-device CPU policy was implemented and withdrawn because the
retained source-matched compiler produced a daemon that exits `139` before CLI
validation.

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
- Build logs:
  `build/simpleos_gpu_host/offload_policy/native-build.out` and
  `native-build-cycle2.out`.

No bootstrap was run. The policy source, protocol reason, tests, and manuals
were withdrawn rather than pushing unverified production behavior. Three
focused native build/run cycles are exhausted.

## Resume

1. Repair or replace the source-matched compiler/runtime route so an
   incrementally rebuilt host daemon passes basic CLI validation without
   unresolved generated helpers or SIGSEGV.
2. Add a calibrated `--processing-min-offload-elements` knob, defaulting to
   the measured 1,048,576-element Linux CUDA break-even; allow `0` to disable.
3. When CPU fallback is enabled and the request is below threshold, publish an
   explicit CPU fallback receipt before device execution. Strict fallback
   `none` must continue executing the requested GPU backend.
4. Run the focused policy contract and native daemon-wire small/large batch
   checks once against the admitted binary.

Owner: Linux GPU host operator. Final reviewer: high-capability model.
