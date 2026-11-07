# In-guest Simple interpreter faults in rt_string_join on nil array (freestanding module-init + optimizer guard fold)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Re-verification (2026-08-10)

Status confirmed unchanged and remains **OPEN — ARCHITECTURAL**.
`scratchpad/laneb_recover/` (where the staged partial fixes were held) no
longer exists in this working copy — scratch state, expected to not persist
across sessions per known scratch-sweep behavior — so the staged patches are
not available to re-verify or land here. Both compounding root causes require
work explicitly out of this sweep's scope: (1) freestanding one-binary
module-init codegen is a `src/compiler` central-compiler change that "must
clear `bin/simple build bootstrap` before landing" — running
`bin/simple build bootstrap` is forbidden by this sweep's hard constraints;
(2) the Rust seed's optimizer guard-fold is a `src/compiler_rust/` change,
also forbidden by this sweep's hard constraints. No `.spl`-only workaround is
available: the fault is in the in-guest interpreter's own runtime C helpers
(`rt_string_join`, `rt_array_len_safe`) and in the freestanding module-init
codegen path itself, not in `.spl` source that a spec-level workaround could
route around. Leaving OPEN/ARCHITECTURAL; re-attempt requires a session that
can run a full bootstrap and touch `src/compiler_rust/`.

**Revalidated 2026-11-02: still plausible because OPEN — blocks the last step of the in-guest Simple compiler port; no merged fix commit with a passing regression is cited in this doc.**

## Re-verification 2026-11-07 (work/simpleos-p1-codegen-20261107) — neither root cause reproduces on the current seed's x86_64 freestanding object path

- **Guard fold (root cause 2):** the "seed inlines rt_array_len and folds
  array_is_valid's guard" mechanism cannot occur: the seed's only MIR
  optimizer, `codegen/mir_inline.rs::is_inline_candidate`, has refused
  `rt_*` callees and any callee with a back edge (array_is_valid has a loop)
  since May 2026, and Cranelift (0.116, `opt_level=speed` for both Standard and
  Aggressive) cannot fold `x < 4096` on an unknown parameter.
  `src/compiler_rust/compiler/tests/entry_closure_defects_x86_64_none.rs`
  (`low_handle_guard_on_i64_param_survives_x86_64_none`,
  `low_handle_guard_inside_inlined_callee_survives_x86_64_none`) compiles the
  `i64`-handle guard shape, directly and through an inlined helper, to an
  `x86_64-unknown-none` Aggressive object and runs it under `qemu-x86_64`
  with a `peek` that exits 99 for a low address and returns 7 otherwise:
  handles 0, 3 and 8 never reach it and handle 65536 does (PASS); deleting the
  guard makes it red (99), and a guard folded to always-reject would miss the
  65536 term, so the probe discriminates both ways.
- **Array initializers (root cause 1):** module-global array initializers
  are emitted for freestanding builds (`__module_init_<module>` from
  `codegen/common_backend.rs::generate_module_init`, aggregated by
  `native_project/linker.rs::generate_init_caller`, which the SimpleOS user
  link path at `linker.rs` `link_objects_freestanding` includes; called from
  `src/os/libc/simpleos_crt0.S:121`). Pinned by
  `baremetal_entry_closure_imported_class_x86_64_none.rs` for a `[u64] = []`
  global.

No product code changed. Unverified: rebuilding
`bin/release/x86_64-unknown-simpleos/simple` and the OVMF `/hello.spl` run.
One residual risk to check then: `src/os/libc/simpleos_simple_runtime.c:230`
defines a STRONG empty `__simple_call_module_inits`, and
`src/os/port/llvm/sysroot.shs:190-192` / `:396-398` copy the compat archive
holding it TO `libsimple_runtime.a` — the archive the seed's SimpleOS user link
consumes — unless the native-runtime step (`:244-248`) later overwrites it. In
a sysroot left on the compat archive, pulling that member alongside the seed's
strong aggregator (`linker.rs` `generate_init_caller`) is a duplicate-symbol
link error (freestanding links pass no `-z muldefs`, `linker.rs:30-36`), not a
silent replacement. Confirm which archive the rebuilt sysroot ships.

Both tests are local-only: CI `rust-tests.yml:112` excludes `simple-compiler`
from `cargo test` (and `:119` builds only `--lib --no-run`), and they need
clang/ld.lld with the X86 target plus `qemu-x86_64`.
