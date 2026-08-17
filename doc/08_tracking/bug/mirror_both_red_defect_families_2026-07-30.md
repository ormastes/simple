# Mirror BOTH-RED population: every failure traces to an already-documented landmine

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Lane MIRR2**, run inline by the orchestrator after two subagent attempts failed
(the first deadlocked on a background monitor, the second was halted on an API
quota).

## Method

- Diverged set recomputed by content hash over `test/unit/**` vs the same path
  under `test/01_unit/**`: **872 diverged** (MIRR1 reported 884; the delta is the
  4 specs MIRR1 repaired plus other reconciliations landed since).
- Selection rule, reproducible: `sort` the diverged list, take **every 97th**
  starting at index 1 → **n=9**.
- Each spec run in BOTH trees, synchronously, one per command:
  `env -u SIMPLE_TIMEOUT_SECONDS timeout 200 bin/simple test --no-session-daemon <spec>`
- **All 18 runs produced a `Results:` line.** Zero "did not execute", matching MIRR1.

## Sample

| # | spec | `test/unit` | `test/01_unit` | class |
|---|---|---|---|---|
| 1 | app/branch_coverage_7 | 78/78 | 75/78 | **MIRROR-AHEAD** |
| 2 | app/mcp_unit/transport_error_handling | 27/27 | 27/27 | COSMETIC |
| 3 | compiler/async/async_integration | 21/21 | 21/21 | COSMETIC |
| 4 | compiler/coverage/branch_coverage_4 | 75/78 | 78/78 | MIRROR-STALE |
| 5 | compiler/types/type_inference | 27/29 | 27/29 | **BOTH-RED** |
| 6 | lib/common/parsers_sdn_coverage | 78/79 | 81/82 | **BOTH-RED** |
| 7 | lib/database/sql/sql_types | 23/44 | 23/44 | **BOTH-RED** |
| 8 | lib/nogc_async_mut_noalloc/async/poll | 1/1 | 2/2 | COSMETIC (differing case counts) |
| 9 | os/kernel/ipc/ipc_port_create_baremetal_stub | 7/7 | 7/7 | COSMETIC |

BOTH-RED 3 | COSMETIC 4 | MIRROR-STALE 1 | MIRROR-AHEAD 1 | NO-EXECUTE 0.
At n=9 these proportions carry no useful precision — the value here is the
clustering below, not the percentages.

## Correction to MIRR1: MIRROR-AHEAD is not zero

MIRR1 reported 0 MIRROR-AHEAD in 25 samples and repaired stale mirrors by
**copying the `01_unit` twin over the mirror**. Sample #1 is the counter-example:
`app/branch_coverage_7_spec.spl` is **78/78 in the mirror and 75/78 in
`01_unit`** — the `01_unit` copy is the stale one. Blind-copying the twin there
would have *introduced* 3 failures.

**Reconciliation direction must be decided per spec by running both sides**, never
assumed. MIRR1's four repairs were each verified green afterwards so they stand,
but the rule it implied ("mirror is behind, copy the twin over it") is wrong as a
general policy.

## Defect families — 3 of 3 are known landmines, 0 new

**Family A — the `.?` exists-check operator lowers to a bool (specs 5 and 7).**

```
# spec 5, type_inference_spec.spl:93
it "infer Some variant":
    val x = Some(42)
    check(x.? == true)          # FAILS: expected false to equal true

# spec 7, sql_types_spec.spl:35
val v = DbValue.Integer(value: 42)
val result = v.as_int()
expect(result.?).to_equal(true)   # FAILS
expect(result?).to_equal(42)      # FAILS: "expected 42 to equal true"
```

This is exactly the documented seed defect: `.?` binds `true` rather than a `T?`,
so the following access sees a bool. It accounts for **21 of the 21 failures in
sql_types** and both failures in type_inference — i.e. the single largest failure
block in the sample comes from one known operator bug.

> **CORRECTION 2026-07-30 (same day): Family A is NOT an engine bug — the specs were wrong.**
> `x.?` **extracts the Option payload**; it is not a boolean exists-check. The
> pure-Simple compiler documents this itself in
> `35.semantics/narrowing.spl:365` — *"ExistsCheck (`x.? -> T`)"* — and the
> 2026-07-25 native fix (`native_exists_check_struct_payload_becomes_bool`)
> deliberately made ExistsCheck keep a **payload** result so `evidence.?.marker`
> works. Both engines agree: `Some(42).?` is `42`, and `x.? == true` is
> `42 == true` → false.
> The assertions were stale relative to that deliberate semantic change. Correct
> idiom is `x != nil` / `x == nil` (verified: `Some(42) != nil` → true,
> `nil != nil` → false).
> Fixed in both mirror copies: **sql_types 23/44 → 44/44, type_inference
> 27/29 → 29/29**, assertion count unchanged (58 in, 58 out).
> **Remaining: 913 live sites across 304 spec files still use the wrong idiom**
> (plus ~600 more inside commented-out placeholder blocks). That sweep is not
> done — it is mechanical but large, and touching 304 spec files at once is a
> repo-owner call.

**Family B — dict read on a present key (spec 6).**

`it "get by key from dict"` fails with `expected true to equal false`, the
documented native `Dict.get()` family (corrupt on hit; a miss returns
`0/false/NULL`, not `nil`).

**New mechanisms found: none.** Every BOTH-RED failure in this sample is a
previously-documented engine defect, not a fault in the code the spec targets.

## Why no fixes were applied

Both families live in the **seed engine**, not in the specs or the modules under
test. `.?` lowering is a Rust-seed defect with an existing bug doc; `Dict.get` is
covered by `doc/07_guide/language/dict_native_pitfalls.md`. There is no minimal,
unambiguous product fix available inside this lane, and rewriting the specs to
dodge `.?` would be hiding an engine bug in test code — the opposite of what this
campaign is for.

## Implication

The BOTH-RED class is **not** a backlog of independent product bugs. On this
sample it is a small number of engine defects projected across many specs. Fixing
`.?` lowering alone would likely turn a large fraction of the ~200 projected
BOTH-RED specs green. That is a far better investment than per-spec repair, and it
argues for fixing the engine before spending any more lanes on mirror triage.
