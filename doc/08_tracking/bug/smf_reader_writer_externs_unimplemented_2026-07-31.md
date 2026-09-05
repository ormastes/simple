# SMF reader/writer externs are unimplemented scaffolding (2026-07-31)

**Found by:** link_manager Lane L1ADAPT while trying to prove the L1 adapter
against a real on-disk `.smf` file.
**Status:** Open. Blocks the LINK lane's "byte-identical SMF output" oracle.

## Evidence

- No `.smf` fixture exists anywhere under `test/` (`find test -iname '*.smf'`
  is empty).
- `rt_smf_reader_open` — the only path that populates
  `SmfReaderImpl.symbols` — has **zero implementations**: the only match in
  the entire tree (including `src/compiler_rust/`, `src/runtime/`, all
  `.rs`/`.c`/`.cpp`) is its own `extern fn` declaration in
  `src/compiler/70.backend/linker/smf_reader.spl`. Per the known
  unregistered-extern behavior it would return nil silently if called.
- `SmfWriter.write()` (`smf_writer.spl`) is a stub: it declares
  `extern fn rt_smf_write` locally and unconditionally returns `Ok([])`.
  Proven executably by
  `test/01_unit/compiler/linker/gpu_smf/smf_reader_adapter_spec.spl`
  ("write-stub proof" example asserts `bytes.len() == 0`).
- Related: `bin/simple compile --format=smf` crashes before reaching any of
  this (`compile_format_smf_nil_receiver_crash_2026-07-31.md`).

## Impact

Phase 1 of `link_manager_plan.md` requires "byte-identical output to the
current SMF linker" — but there is no current in-repo SMF byte producer or
consumer that actually runs. Until the writer/reader are implemented (or the
plan's oracle is re-scoped to the native-build/cc route the parity harness
already verified), SMF-level parity cannot be gated. The L1 adapter therefore
targets the writer-side `SmfWriterSymbol` structures, which are real and
exercised.
