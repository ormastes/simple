# P1 `compiler` rows, first half by id — session triage 2026-08-18

Scope: the 29 lowest-id `compiler`/P1 rows in `doc/08_tracking/todo/todo_db.sdn`
(ids 536..605). Worktree `/mnt/data/worktrees/p1-compiler-a`, `bin/simple` = the
shared **Rust seed** (`Simple Language v1.0.0-RC`, self-identified as
bootstrap-seed-only). Host: 32 cores, load 6.5-10, ~25 concurrent `simple`
processes.

## Already closed before this session (no action)

| row | status |
|---|---|
| 582 | `done, false` |
| 592 | `done, true` — resolved 2026-08-18 via the "localize the counter" option |
| 605 | `done, false` |

## Worked this session

| row | outcome |
|---|---|
| 559 | **FIXED + closed.** Premise partly wrong: not a MIR lowering defect at all. See `rfind_sentinel_vs_optional_contract_split_2026-08-18.md`. |
| 561 | **Premise correction, stays open.** Its recorded blocker no longer reproduces (see below). |
| 597 | Named spec re-run to test its "fails all six examples" claim; see the row's own note for the verdict. |

### Row 561 — recorded blocker does not reproduce

The row states the focused run "is blocked because the canonical release binary
identifies as the Rust seed and aborts on unknown extern `rt_cli_arg_count`".
Re-run this session:

```
bin/simple test test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl
Results: 8 total, 8 passed, 0 failed          (exit 0)
```

No abort, no `rt_cli_arg_count` error. The row remains open for the one honest
reason left: that harness run exercises the **Rust seed** parser, not the
pure-Simple parser the row names.

## Not attempted — blocked by this session's constraints, NOT by evidence

These are left open deliberately. None was reproduced, so none should be read
as confirmed-still-broken; equally none was disproved.

**Requires rebuilding the Rust seed** (out of scope: `bin/simple` is a shared
symlink into another session's worktree and must not be rebuilt or replaced):
rows **557** (lexical `unsafe` scope enforcement in the seed), **558**, **560**,
**562**.

**Requires a source-matched non-seed pure-Simple compiler / Gate 73 / Gate 84**
— rows **572**, **584**, and the whole "bounded worker" chain **589, 590, 591,
593, 594, 595, 596, 598, 599, 600, 601, 602, 603, 604**. Row 584's own note
records the last such build timing out at 900s with no artifact. Producing that
compiler is a bootstrap-lane activity owned elsewhere.

**Board / cross-arch lanes excluded by standing decision** (AArch64 and riscv64
SimpleOS builds, QEMU board bring-up): rows **536**, **540**, **548**.

One cheap static observation on row **540**, recorded so the next session does
not have to redo it: a scan of `src/compiler/70.backend/**.spl` finds **no**
cfg-gated global-value filtering of any kind (no `cfg`+`global`/`dedup`/
`filter`/`gate` co-occurrence), so the row's premise — that duplicate
target-gated globals are not filtered before native symbol resolution — is at
least still structurally true. That is a code-shape observation, **not** a
reproduction of the AArch64 PCI/ECAM misselection.

## The three pending runs — RESOLVED, and an earlier attribution CORRECTED

An earlier revision of this file recorded the three detached runs as blocked by
"host throughput". **That attribution was wrong and is retracted.** All three
subsequently completed, and the process evidence contradicts a throughput
explanation: while apparently stalled they sat in state `S` with **4 seconds of
CPU consumed over 11m45s elapsed**, i.e. blocked rather than compute-starved,
with the box's load average down at 4.15 on 32 cores. They were waiting, not
queuing.

### Regression gap on the row-559 fix: CLOSED, green

Both pre-existing specs covering the three modules the fix touched pass:

```
test/01_unit/lib/std/shell/path_spec.spl
    outcome=OK declared>=23 executed=23 passed=23 failed=0 skipped=0 dropped=0
    Results: 23 total, 23 passed, 0 failed

test/01_unit/lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl
    outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0
    Results: 2 total, 2 passed, 0 failed
```

The row-559 fix therefore introduces no regression in existing coverage. This
was the one genuine open gap flagged earlier; it is now closed.

### Row 597: still INCONCLUSIVE, but the row's claim is not what happens

```
SPEC FILE VERDICT: test/01_unit/compiler/hir/resolve_import_symbols_spec.spl
    declared>=1 executed=1 passed=0 failed=1 dropped=0
    timeout=1 reason=child-timeout budget_ms=900000
Results: 0 total, 0 passed, 0 failed          (exit 5)
```

`Results: 0 total` is **not** a pass and not a refutation — nothing executed. But
note the shape: the row claims the spec "fails all six examples". It does not
reach six examples at all; the child **times out after the full 900s budget**
with zero tests executed. Whatever is wrong is a hang, not six assertion
failures, so the row's description should not be trusted as a starting point.
Row 597 stays open; the next session should attack the hang (isolate one
provider/consumer fixture, as the row already suggests) rather than chase
assertion failures that were never observed.

