# `next_p1_digit_index`: Optional tagged-slot review

Status: **SOURCE-FIXED-PROOF-PENDING** (2026-09-22)

The original P1 reported `text.index_of("3")` at zero-based position `3` as
nil because a primitive `i64?` slot carried raw `3`, the runtime nil word.
No new source patch is warranted for the reproducer on campaign head
`682c019d147`: the current MIR boundary already stores scalar `T?` slots as
tagged `RuntimeValue`s.

## Source proof

`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs` defines
`slot_holds_tagged_value`, `box_scalar_for_tagged_slot`, and
`unbox_scalar_for_raw_slot`. `HirType::Pointer { inner: scalar }` (the HIR
form for `T?`) is explicitly a tagged slot. The helper boxes raw scalars at
declared optional/erased boundaries and unboxes only when the declared target
is raw. This explains the observed reproducer fix and avoids the historically
rejected one-sided `??` patch.

The matrix does not yet prove every ABI consumer: `if val`, assignment, field
stores, optional chains, and cross-function calls still require an admitted
Windows self-hosted receipt. This is why the status remains proof-pending.

## Windows executable proof

Fixture: `test/fixtures/compiler/next_p1_digit_index_matrix.spl`.

It has 16 self-checking cases: the exact digit-index `Some(3)` reproducer with
arithmetic after `??`, neighbouring `2`/`4` integer controls, direct scalar
Optional controls, text, nil, legacy text-index `-1` miss, and `Result`
discriminant controls. Any mismatch prints `FAIL` then triggers an assertion,
so the process exits nonzero.

| backend | result | elapsed | peak RSS |
|---|---:|---:|---:|
| `SIMPLE_EXECUTION_MODE=interpreter` | 16 PASS | 625 ms | 18,706,432 bytes |
| `SIMPLE_EXECUTION_MODE=jit` | 16 PASS | 506 ms | 20,496,384 bytes |

Both runs used `bin/simple.exe run` in the isolated Windows worktree. The
binary identifies itself as the Rust bootstrap seed; this proves the legacy
JIT lane named in the report, while the production self-hosted Stage 4 binary
still needs a separately admitted Windows receipt before this status can become
fully fixed.

Host: Windows on a 12th Gen Intel Core i9-12900 (16 cores, 24 logical
processors). The short fixture exercises front-end lowering and JIT dispatch;
its elapsed time and RSS are smoke evidence, not a performance target.
