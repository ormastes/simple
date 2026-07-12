# Bootstrap Stage 4 imported-call and runtime gap

The 2026-07-12 full bootstrap proves Stage 2 and Stage 3 succeed through the
pure-Simple compiler. Stage 4 then fails while linking the full CLI.

Two independent owner bugs remain:

1. imported Simple calls such as `run_check` and `run_arch_check` are emitted
   bare although the compiled objects define module-qualified symbols;
2. the full compiler CLI selects the core-C runtime, which does not provide
   hosted compiler services such as `rt_array_concat`,
   `rt_process_run_timeout`, `spl_dlsym`, and `spl_wffi_call_i64`.

TODO: reuse the existing unique bare-to-qualified alias analysis at the hosted
ELF linker boundary (or fix call-target mangling at its canonical owner), then
allow `native_all` only as selective backfill for the compiler-like CLI entry.
Do not generate symbol stubs, add feature-local `rt_*` aliases, or re-enable a
hosted runtime bundle for ordinary applications.
