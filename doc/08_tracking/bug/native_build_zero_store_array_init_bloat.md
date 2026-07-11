# BUG: all-zero static array initializers lower to N inline zero-stores (13.5 MB dead text in merged kernel)

**Status:** open
**Severity:** medium (binary bloat: 13.5 MB of 22.6 MB merged-kernel text is dead init code; also slows boot-time module init where it runs)
**Component:** native-build codegen — module-level static array initializer lowering
**Found:** 2026-07-11 (UEFI merged-kernel lane, while diagnosing the 22.6 MB text anomaly)

## Symptom

`__module_init_kernel__fd_table` is 8.5 MB and `__module_init_kernel__pipe_compat` 5.0 MB of .text. Cause: `fd_table.spl` declares seven `[T; 65536] = [0; 65536]` module-level arrays and `pipe_compat.spl` one `[u8; 262144] = [0; 262144]`; the compiler emits one store per element instead of relying on `.bss` zeroing (the arrays already live in `.bss`, which crt0 zeroes). In freestanding images these module inits are additionally stubbed/never called — the code is pure dead weight.

## Fix direction

All-zero static array initializers should emit NO per-element stores (the .bss guarantee covers them); non-zero constant initializers should use a data-section image + memcpy or a fill loop, never unrolled element stores at this scale.

## Related second bug (separate repro)

The seed **segfaults** when compiling an uninitialized module-level `var x: [T; N]` (no initializer) — which is the natural workaround for this bloat. Filed as `seed_segfault_uninit_module_array_var.md`.
