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
passing median self-test. The resumed first strict daemon link exposed the
retained runtime's missing `rt_char_from_code` and accidental `str.byte_at`
closure. Reusing exported `rt_bytes_to_text` on already-validated byte
sequences and snapshotting `.bytes()` removed both dependencies; cycle 2 linked
with `4 compiled, 213 cached, 0 failed`.

That binary still failed before readiness. Its generated `common.string_core`
object compiled same-named method wrappers into self-calls or infinite loops.
The source now follows the canonical compiler-core pattern and routes length,
slice, character access, contains, prefix/suffix, and find/rfind directly to
runtime externs. Rust runtime gained the missing `rt_string_contains` wrapper
over byte-correct `rt_string_find`; its focused test passes, and the refreshed
CUDA/Vulkan runtime archive exports both string predicates. Cycle 3 linked with
`2 compiled, 215 cached, 0 failed`, but retained-cache object disassembly still
showed the prior `str_len` infinite loop and the live daemon again missed
transport readiness.

The next retained-cache rebuild compiled the complete wrapper source with `4
compiled, 213 cached, 0 failed`. Its generated `string_core` object has zero
primitive self-relocations and zero jump-to-self bodies, and the daemon reaches
CLI validation. The first live HELLO then exposed trait-erased render-probe
shutdown dispatch. Moving probe creation and concrete shutdown into the
platform owners rebuilt with `4 compiled, 213 cached, 0 failed` and admitted
one CUDA device receipt.

The wire probe initially compared that receipt with the direct executor's raw
64-bit checksum rather than the protocol's modular checksum. The strict probe
rebuild (`4 compiled, 15 cached, 0 failed`) fixed that expectation. The
preserved third-cycle receipt proves status `1`, reason `0`, device source `1`,
handle `1`, positive identity, `4,194,304` output bytes, and exact correlation,
but every readback word is `135272480` instead of `16909060`. The payload word
is correct on the wire. A strict retained-cache build of `words[5] as u32`
completed at `3 compiled, 214 cached`, but preserved the same 8x result. A
second build read the scalar through the existing ABI-exact `raw_read_i32`
facade (`2 compiled, 215 cached`) and again preserved the same result.

Generated daemon-runner code for the second build passes the exact raw `u32`
unchanged into `processing_ir_fill_u32`; the runtime archive's
`rt_ptr_read_i32` is a direct 32-bit load. The retained cache nevertheless
contains older flattened entry-module copies, consistent with TODO 562's
missing transitive dependency hashes. A one-module entry refresh (`1 compiled,
216 cached`) still stopped at request 1, but the wrapper deleted that final
receipt. The probe now reports status, reason, source, checksum, bytes, timing,
first output word, receipt validity, and output parity on failure.

The rebuilt diagnostic probe proved the sole failure was parity:
`last_receipt_valid=true`, status `1`, reason `0`, source `1`, positive
handle/identity, checksum `33620483`, and first word `135272480`. A clean
217-module isolated-cache daemon then crashed during HELLO. Its captured
addresses map through `Engine2D.shutdown()` into
`SimpleOsGpuHostAllPlatform.shutdown()` and CUDA teardown, proving trait-vtable
misdispatch. Engine2D now shuts retained CUDA, Vulkan, Metal, OpenCL, ROCm, and
software backends through concrete fields before its trait fallback. The
strict rebuild (`2 compiled, 215 cached`) restores a valid correlated CUDA
receipt.

That fresh receipt remains 8x, ruling out stale cache as the value cause.
Disassembly shows `rt_u32s_from_raw` stores tagged `RuntimeValue::from_int`
elements while the native readback/checksum loop loads each slot as an unboxed
u32. Source now replaces the million-iteration Simple copy/checksum loop with
`rt_write_u32s_to_raw_checksum`, which decodes each runtime element once,
writes exact raw u32 words, and computes the protocol checksum in the same
pass. Its focused Rust test passes bit-exact, count-bounded, null, and
out-of-range cases.

## Result

The incrementally rebuilt CUDA/Vulkan runtime archive exports
`rt_write_u32s_to_raw_checksum`, and the isolated daemon relinks with `4
compiled, 213 cached, 0 failed`. The documented device-warm wrapper passes all
eight requests: three warmups and five measured exact 1,048,576-element CUDA
requests with checksum `809508928`, first word `16909060`, positive stable
handle/identity, and no fallback.

Measured medians are `155110 us` device, `312012 us` round trip, `156902 us`
non-device overhead, and `82097 us` for the independent CPU oracle. Every
receipt is correctly classified `available-not-preferred`; correctness and
device provenance do not override the measured offload policy.

Evidence was built from source revision `1948920dadc4`. Retained logs:
`build/simpleos_gpu_host/device_warm_wire/runtime-build-bulk-readback.log`,
`daemon-build-bulk-readback.log`, `wrapper-device-warm-bulk-readback.log`, and
`daemon-live-bulk-readback.log`. The adjacent
`evidence-provenance-bulk-readback.env` binds that full revision to SHA-256
hashes for the runtime archive, daemon, and probe.

Owner: Linux GPU host operator. Final reviewer: high-capability model.
