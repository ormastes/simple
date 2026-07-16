# Bootstrap Stage 4 imported-call and runtime gap

The 2026-07-12 full bootstrap proves Stage 2 and Stage 3 succeed through the
pure-Simple compiler. Stage 4 then fails while linking the full CLI.

Two independent owner classes remain:

1. imported Simple calls such as `run_check` and `run_arch_check` are emitted
   bare although the compiled objects define module-qualified symbols;
2. the full compiler CLI needs capability-owned providers beyond core-C, such
   as `rt_array_concat`, `spl_dlsym`, and `spl_wffi_call_i64`.

The POSIX/macOS/BSD core-C owner now provides `rt_process_run_timeout` with the
canonical tagged tuple ABI, concurrent stdout/stderr capture, monotonic timeout,
and process-group cleanup. The Windows source path uses restricted inherited
stdio handles, suspended launch, and a kill-on-close Job Object for descendant
cleanup. Windows compile/native proof and strict LLVM/Cranelift execution remain
pending, so this closes source ownership only; POSIX parity is not Windows proof.

The duplicated `ffi_gen.specs/process_mod.spl` timeout entries and
`sffi_gen.templates/simple_sffi.h` still describe a legacy generated string ABI
and are not the production native call-lowering owner. They remain a separate
generator cleanup; production is locked by the four-register `runtime_sffi.rs`
contract and text/array expansion mapping.

TODO: reuse the existing unique bare-to-qualified alias analysis at the hosted
ELF linker boundary (or fix call-target mangling at its canonical owner), then
route remaining symbols through the exact Stage4 provider profile. Do not
select raw `native_all`, generate symbol stubs, add feature-local `rt_*` aliases,
or re-enable a hosted runtime bundle for ordinary applications.
