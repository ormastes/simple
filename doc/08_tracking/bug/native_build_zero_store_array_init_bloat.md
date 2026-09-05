# BUG: all-zero static array initializers lower to N inline zero-stores (13.5 MB dead text in merged kernel)

**Status:** RESOLVED (2026-07-11)
**Severity:** medium (binary bloat: 13.5 MB of 22.6 MB merged-kernel text is dead init code; also slows boot-time module init where it runs)
**Component:** native-build codegen — module-level static array initializer lowering
**Found:** 2026-07-11 (UEFI merged-kernel lane, while diagnosing the 22.6 MB text anomaly)

## Symptom

`__module_init_kernel__fd_table` is 8.5 MB and `__module_init_kernel__pipe_compat` 5.0 MB of .text. Cause: `fd_table.spl` declares seven `[T; 65536] = [0; 65536]` module-level arrays and `pipe_compat.spl` one `[u8; 262144] = [0; 262144]`; the compiler emits one store per element instead of relying on `.bss` zeroing (the arrays already live in `.bss`, which crt0 zeroes). In freestanding images these module inits are additionally stubbed/never called — the code is pure dead weight.

## Fix direction

All-zero static array initializers should emit NO per-element stores (the .bss guarantee covers them); non-zero constant initializers should use a data-section image + memcpy or a fill loop, never unrolled element stores at this scale.

## Related second bug (separate repro)

The seed **segfaults** when compiling an uninitialized module-level `var x: [T; N]` (no initializer) — which is the natural workaround for this bloat. Filed as `seed_segfault_uninit_module_array_var.md`.

## Resolution (2026-07-11)

All-zero array initializers ([0; N]) now emit one compact runtime fill loop
(`for i in 0..N { rt_*_push(array, 0) }`) instead of N unrolled push calls —
code size O(1) per array, semantics identical (handle still created and filled
to length N; boxed zero `0 << 3` == raw 0). Fixed in BOTH backends — the SSH
merged kernel is built with cranelift, and LLVM had the same unroll:

- `src/compiler_rust/compiler/src/codegen/common_backend.rs` — cranelift:
  `emit_zero_fill_push_loop` + all-zero detection in the module-init array loop.
- `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs` — LLVM:
  `emit_zero_fill_loop`, same wiring.
- Regression: `jit_tests.rs` `test_jit_module_init_all_zero_array_compact_fill_loop`
  (asserts len==100000, [123]==0, [99999]==0, and nonzero [1;8] unaffected).

Verified: merged-kernel .text 28,376,200 → 9,396,968 B (−18.98 MB;
`__module_init_kernel__fd_table` 8,544,641 → 2,221 B, `pipe_compat`
4,986,934 → 549 B); ssh_clang_hello_ring3.shs DEMO PASSES on the shrunk
kernel; simple-compiler --lib zero net-new failures (2877/240 → 2881/237).
