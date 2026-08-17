# SimpleOS rv64 link aliases lost call targets (`unknown_N`) to real functions via `--defsym`

- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 04).
- **Severity:** HIGH (latent memory-safety / wrong-signature calls)
- **Area:** `src/compiler/70.backend/backend/llvm_native_link.spl`, SimpleOS riscv64 link
- **Filed:** 2026-07-28

## Summary

`link_simpleos_riscv64` unconditionally aliases thirteen `unknown_0..unknown_12`
symbols onto five real kernel functions using `ld` `--defsym`, on the real-kernel
link path. `unknown_N` is not an intentional extern — it is the placeholder the
MIR lowering emits when a callee symbol resolves to an **empty name**, i.e. a
*lost call target*. Aliasing them makes the link succeed while re-pointing lost
calls at unrelated functions with incompatible signatures.

## Location

`src/compiler/70.backend/backend/llvm_native_link.spl:2370-2383`, guarded by
`if not is_smoke_entry and not uses_freestanding_runtime:` — that is, the real
kernel path, not the smoke path.

The thirteen aliases collapse onto five distinct targets:

| alias | target |
|---|---|
| `unknown_0`, `unknown_5` | `rt_riscv_uart_put` |
| `unknown_1`, `unknown_10`, `unknown_12` | `_uart_put` |
| `unknown_2` | `rt_riscv_qemu_reserved_end` |
| `unknown_3` | `rt_riscv_qemu_ram_base` |
| `unknown_4` | `rt_riscv_qemu_heap_size` |
| `unknown_6`, `unknown_8` | `_boot_banner` |
| `unknown_7` | `rt_riscv_qemu_ram_size` |
| `unknown_9` | `log_raw_println` |
| `unknown_11` | `rt_riscv_noalloc_pmm_init` |

## Root cause of the `unknown_N` names

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2708` emits

    name = "unknown_{self.symbol_id_value(symbol)}"

when a callee symbol has an empty name. So each `unknown_N` marks a call whose
target the compiler failed to resolve. The correct fix is upstream — resolve the
callee — not to paper over the unresolved reference at link time.

## Why this is worse than a nil stub

A weak nil-returning stub yields an obviously-wrong value that a nil check can
catch. An alias yields a **valid function with the wrong signature**:

- `unknown_9` → `log_raw_println` casts argument 0 to `char*` and walks it. If the
  lost call site passed a non-pointer, this is an **arbitrary read** until it
  finds a NUL.
- `unknown_2`, `unknown_3`, `unknown_4`, `unknown_7` → RAM-geometry accessors that
  return plausible RAM addresses. A downstream nil check **passes**, where a nil
  stub would have failed it. The corruption therefore survives exactly the
  defensive check most likely to be present.

## Fragility: the alias table is keyed on stale symbol IDs

`symbol_id_value(symbol)` is a compiler-internal symbol ID captured from **one
historical build**. Any source edit renumbers symbol IDs, so `unknown_7` in a
future build is almost certainly a different lost call site than the one this
table was written against — while the `--defsym` still silently re-points it.
The table cannot be kept correct by construction; it is correct only for a build
that no longer exists.

## Current exposure

Inert but armed. Both shipped artifacts —
`build/os/simpleos_riscv64_smf_fs.elf` and `build/os/simpleos_riscv32_smf_fs.elf`
— are `spl_start` smoke builds, so `is_smoke_entry` is true and the block does
not fire. Verified: `nm` reports **0** `unknown_N` symbols in either ELF. The
block fires the moment a non-smoke real-kernel rv64 link is performed.

## Provenance

The block is present as of commit `37cda4befdc`. Caveat on attribution: that
commit is `fix(vcs): restore main from pushed jj conflict tree`, a bulk
restoration after the jj-conflict-tree incident, so it is the commit that put
this text on `main` but not necessarily where the code was originally authored.

## Suggested fix

1. Delete the `--defsym=unknown_*` block. A lost call target must fail the link.
2. Fix the upstream resolution failure that makes
   `method_calls_literals.spl:2708` emit an empty-name callee.
3. Add a link-time assertion that no `unknown_[0-9]+` symbol is referenced by any
   SimpleOS link, on every arch.

## Related

- `doc/08_tracking/bug/simpleos_fabricated_rt_guard_weak_real_false_positive_2026-07-28.md`
  — the fabricated-`rt_*` link guard intended to cover the adjacent fail-open
  class on x86_64.

## 2026-08-17 — fail-closed: unknown_N no longer aliased onto real functions

Status: FIXED (link-path half).

Root cause chain, both ends verified against current source on 2026-08-17:

1. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3396`
   `symbol_to_operand` names an unresolvable callee `unknown_<symbol-id>`.
   That is the correct loud behaviour: it reaches the linker undefined.
2. `src/compiler/70.backend/backend/llvm_native_link.spl:3115-3128` silenced it
   with thirteen `--defsym=unknown_N=<real kernel function>` arguments on the
   REAL-KERNEL riscv64 path (`not is_smoke_entry and not
   uses_freestanding_runtime`), mapping the unknowns onto five functions with
   unrelated signatures: `rt_riscv_uart_put`, `_uart_put`, `_boot_banner`,
   `log_raw_println`, `rt_riscv_noalloc_pmm_init`, plus three
   `rt_riscv_qemu_*` accessors. A call the compiler failed to resolve jumped
   into an unrelated function with whatever was in the argument registers.

Fix: all thirteen now defsym to `__simple_unresolved_call_trap`, a new function
emitted into the generated riscv64 stub source (same function that builds the
defsym list). It writes a message to the UART and halts on `wfi`.

Why this needed no latent-breakage measurement: the set of DEFINED symbol names
is unchanged, so every link that resolved before still resolves. The change is
confined to what happens when a lost call is actually TAKEN at runtime — a halt
with a message instead of silently running another function.

Not proven: that no riscv64 kernel currently depends on one of these aliases
being taken and behaving benignly. Reaching a trap on a real kernel boot would
be evidence of a lost call, not a regression of this change.

Spec: `test/01_unit/compiler/backend/unresolved_symbol_alias_fails_closed_spec.spl`
(similar-problem detection: pins the RULE that no unknown_* may be aliased to a
working function, not just the thirteen known sites).
