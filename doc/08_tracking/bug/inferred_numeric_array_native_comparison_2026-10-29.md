# Inferred numeric-array comparison differs from explicit i64 array

Status: OPEN; scoped producer discrepancy, exact lowering cause unproven.

Producer: retained pure-Simple Cranelift compiler
`e3a7e65cdad2aea37939056f5f115053733e342a89f0507eaec3ede9212233d6`.
The process-capture byte probe initially declared `val expected = [65, 237,
149, 156, 234, 184, 128, 240, 159, 153, 130]` and compared each element against
`rt_ptr_read_u8` while the literal text owner remained alive. The native artifact
returned `FAIL retained UTF8 bytes` before invoking either process provider.

LLDB independently verified byte length 11, a nonzero borrowed pointer and
all exact bytes of `A한글🙂`. Rebuilding with `val expected: [i64]` and the
same eleven values passed both literal and owned-text byte comparisons. The
only other changed assertion was a later unbounded-stderr expectation, which
the failing artifact never reached. The exact failing array element and
generated comparison remain to be localized; do not claim a general type
inference repair from the explicit annotation.

- Failing native artifact: `/tmp/simple-process-capture-pure-probe2-20261029/simple_probe`,
  SHA256 `03007aa67b0446f3145ed02cfbedcb912e29d0e189411fef84ccd3bcb143a50f`.
- Corrected typed oracle: `test/01_unit/compiler/driver/process_capture_text_bridge_probe.spl`.
- Passing native artifact: `/tmp/simple-process-capture-pure-probe3-20261029/simple_probe`,
  SHA256 `27d53e987ffbd2ba68f3c3e455ead4430507161be735a01aa6534a6ca5fae3ff`.
- Debugger evidence: `/tmp/simple-phase2-lldb18/bridge-values.log`.
- Bootstrap Rust producer compiled the inferred probe and passed its byte
  checks, exposing a separate unbounded-stderr expectation afterward. Its
  diagnostic evidence is `/tmp/simple-process-capture-seed-probe-20261029`.

The explicit annotation retains the full byte contract; it is not evidence
that the compact inferred form works on this retained producer.
