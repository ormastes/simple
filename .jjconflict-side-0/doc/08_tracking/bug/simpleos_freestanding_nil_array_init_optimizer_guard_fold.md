# In-guest Simple interpreter faults in rt_string_join on nil array (freestanding module-init + optimizer guard fold)

**Target:** `bin/release/x86_64-unknown-simpleos/simple` (the in-guest Simple
interpreter, cross-built with the Rust seed for x86_64-unknown-simpleos).
**Status:** OPEN — blocks the last step of the in-guest Simple compiler port.
The binary BUILDS (3.8 MB static ELF, PT_LOAD 0x40000000, clear of the OVMF
kernel `.bss` band) and RUNS on the OVMF board proxy (no `-kernel`): ring-3
entry, streams its own ELF from NVMe, argv frame (argc=2), opens and reads
`/hello.spl` (39 bytes) — then faults.

## Fault

Interpreter eval faults in `rt_string_join` on a nil / raw-0 array handle
(cr2=0x8) during the `print` path.

## Root cause (two compounding defects)

1. **Freestanding one-binary builds do not run module-global array
   initializers.** A module-level `val X: [T] = [...]` reaches runtime as a
   nil/raw-0 handle, so nil arrays flow into runtime string helpers
   (`rt_string_join` and siblings). (Same class as the Lane A finding that
   module-level `[text]` initializers don't run under freestanding
   native-build — but here it hits the interpreter's own runtime.)
2. **The Rust seed's optimizer folds away defensive guards on already-`i64`
   handle params.** Both `array_is_valid`'s internal guard and an explicit
   `if array < 4096` guard in `rt_string_join` were dropped by the optimizer
   because the param is typed `i64`. The `rt_array_len_safe` guard survived
   ONLY because its param is `[T]`-typed (the cast `array as i64` prevents the
   fold).

## Fix directions (pick one; both are outside a narrow-scope patch)

- **Codegen:** make freestanding one-binary module-init actually run the array
  initializers, so nil arrays never reach the helpers. Cleanest; also fixes
  the Lane A class of bug at the source.
- **Interpreter:** stop passing nil arrays into `rt_string_*` (audit the many
  call sites), OR type the runtime string-helper params as `[T]` (not `i64`)
  so the surviving-guard trick applies uniformly — the optimizer won't fold a
  guard behind an `as i64` cast.

## Evidence + staged fixes

Board evidence, the built binary, build log/stamp, and the partial fixes
(core_string.spl guard + pure-Simple rt_string_chars/rt_lexer_source_set/
rt_lexer_source_slice; llvm_codegen_adapter.spl llvm_translate_module_direct_ir;
rt_array_len_safe nil-safety in parser/lexer/lexer_struct/decl_nodes; current
crt0.o) are HELD in `scratchpad/laneb_recover/` — they are central-compiler
changes that must clear `bin/simple build bootstrap` before landing, which the
in-progress toolchain redeploy currently blocks. Harness to reproduce:
`scripts/os/fsexec_mkimg_simple.spl` + `scripts/os/ssh_simple_hello_uefi.shs`
(OVMF board gate, landed).
