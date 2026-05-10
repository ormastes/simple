# Phase 7 Silent-Green Pre-Scan: dbfs-integration

**Feature:** dbfs-integration
**Phase:** 7-verify (pre-scan agent, runs concurrently with Phase 6 refactor)
**Date:** 2026-04-28
**Scope:** `test/dbfs/*.spl` (21 files; verify_plan §0.2 expected count matches)
**Mode of evidence:** static grep + read-only inspection (no `bin/simple test`, no `git`/`jj`)
**Source-of-truth:** `.sstack/dbfs-integration/verify_plan.md` §5 (11 detector patterns), `.sstack/dbfs-integration/state.md`
**Memory refs:** `feedback_compile_mode_false_greens`, `feedback_no_coverups`

---

## 0. Executive Summary

| Metric | Value |
|---|---|
| Specs scanned | 20 `_spec.spl` + 1 harness (`power_cut_harness.spl`) = 21 files |
| Patterns checked | 11 / 11 (patterns 9 + 10 partially DEFERRED — out of scope without git/test runs) |
| BLOCKING findings | **1** |
| WARN findings | **3** |
| NOTE findings | **3** |
| In-flux deferred | 1 (`dbfs_hw_passthrough_spec.spl` — Phase 6 refactor target; statically inspected anyway, no findings) |

**Bottom line:** one BLOCKING tautology in `bench_harness_smoke_spec.spl:71` must be rewritten before Phase 8 ship. Three WARNs (state.md drift, smoke-spec duplication of intent, harness-style helper expect) and three NOTEs (false-positives + scope flags) for hygiene. Deferred patterns 9 (git diff) and 10 (test runner output) require an executor agent with git/test access — not blockers, but downstream Phase 7 must close them.

---

## 1. Pattern-by-Pattern Findings

### Pattern 1: `skip()` / `pending()`

**Result:** 0 hits.

| File | Line | Match |
|---|---|---|
| _none_ | — | — |

Already verified by Phase 5 `feedback_no_coverups` discipline. Confirmed.

---

### Pattern 2: `it`-blocks with no `expect()` call

**Result:** 1 grep hit, classified WARN (helper-delegated, see analysis).

| File:Line | `it` text | Severity | Analysis |
|---|---|---|---|
| `test/dbfs/arena_as_blob_backend_spec.spl:42` | `"general-mutable arena passes full conformance suite"` | WARN | The it-block body is `run_conformance_suite(0)`. The free function `run_conformance_suite` (lines 19-39) contains **7 `expect(...)` calls** that DO execute when the helper is invoked. Pattern grep is naive (line-local). Real assertions exist; severity not BLOCKING. |

**Counter-mitigation:** Either (a) inline at least one assertion in the it-block to satisfy line-local readers, or (b) add a comment `# expects executed via run_conformance_suite()` for clarity. Not a real silent-green.

---

### Pattern 3: Tautological `expect(true).to_equal(true)` / `expect(x).to_equal(x)`

**Result:** 2 grep hits — split into 1 BLOCKING + 1 WARN (state.md drift).

| File:Line | Match | Severity | Analysis |
|---|---|---|---|
| `test/dbfs/bench_harness_smoke_spec.spl:71` | `expect(true).to_equal(true)` | **BLOCKING** | File is `*_spec.spl` so test runner discovers it. The it-block "metadata_storm over DBFS completes for 10 files" exercises 10 open/unlink cycles via `.unwrap()` (which would throw on Err), but the closing assertion `expect(true).to_equal(true)` is **pure tautology**. Per `feedback_compile_mode_false_greens`, this passes in any mode regardless of any real failure that doesn't manifest as a thrown unwrap. |
| `test/dbfs/bench_harness.spl:270` | `expect(true).to_equal(true)` | WARN | File name does NOT end in `_spec.spl`. Per `state.md > 4-spec > Spec Corrections Applied`, the test runner only discovers `*_spec.spl`, and Phase 4 claimed all describe/it blocks were stripped from `bench_harness.spl`. **They were NOT stripped** — lines 259-283 still contain `describe "BenchHarness — smoke (metadata storm, 10 files)"` with 3 it-blocks. Since not discovered, this isn't an active silent-green; it's dead test code + state.md drift. |

**Counter-mitigation BLOCKING:**
Replace `bench_harness_smoke_spec.spl:71` `expect(true).to_equal(true)` with an assertion on observable state, e.g.:
```
val readdir = mt.readdir("/data").unwrap()
expect(readdir.len()).to_equal(0)   # 10 created, 10 unlinked
```
Or simpler: count successful unlink results inline.

**Counter-mitigation WARN:**
Strip `bench_harness.spl` lines 259-283 (the dead describe block) AND fix the state.md note to match reality, OR rename the file to drop the `.spl` suffix. Either way, reconcile state.md `4-spec` section with the actual file content.

---

### Pattern 4: Stub `Result.Ok(0)` returns from production code paths

**Result:** 0 hits in test scope. **DEFERRED for impl scope.**

verify_plan §5.4 targets `src/lib/nogc_sync_mut/db/` — that path is **forbidden by my task scope** ("DO NOT touch `src/lib/nogc_sync_mut/db/**`"). I scanned only `test/dbfs/*.spl` for the same pattern and got 0 hits.

| File:Line | Match | Severity |
|---|---|---|
| _none in test scope_ | — | — |

**Recommendation:** A separate Phase 7 executor with broader scope must run the verify_plan §5.4 grep against `src/lib/nogc_sync_mut/db/` and `src/lib/nogc_sync_mut/fs_driver/`. Note this scope gap explicitly in `state.md > 7-verify` so it isn't silently dropped.

---

### Pattern 5: TODO/FIXME/XXX adjacent to `expect()`

**Result:** 1 grep hit — false-positive.

| File:Line | Match | Severity | Analysis |
|---|---|---|---|
| `test/dbfs/dbfs_posix_shim_spec.spl:42` | `mt.write(fh, "XXXXXXXXXX").unwrap()` | NOTE (false-positive) | The grep matched the literal string `"XXXXXXXXXX"`, which is filler payload data for a pwrite test (see line 47: `expect(got[0]).to_equal('X')`). Not a TODO/FIXME comment. **Excluded.** |

No genuine TODO/FIXME comments adjacent to expects.

---

### Pattern 6: Compile-mode escapes (`--mode=native` / `--mode=smf`)

**Result:** 0 hits.

| File:Line | Match |
|---|---|
| _none_ | — |

All 21 specs run in interpreter mode only, per `feedback_compile_mode_false_greens`. Confirmed.

---

### Pattern 7: `describe` blocks with 0 `it`-blocks

**Result:** 0 hits among `*_spec.spl` files.

| File | describe count | it count | Severity |
|---|---|---|---|
| `power_cut_harness.spl` | 0 | 0 | NOTE (expected) — not a spec file; per its own header line 1: "Shared harness module — not a spec file" |

Every other file has at least 1 describe and at least 2 its. No empty describe blocks.

---

### Pattern 8: Vacuous matchers (`to_be_truthy()`, `to_not_throw()`)

**Result:** 0 hits.

| File:Line | Match |
|---|---|
| _none_ | — |

The codebase doesn't use `to_be_truthy`/`to_not_throw` matchers in DBFS specs. The only "vacuous-looking" form is `expect(<bool-expr>).to_equal(true)`, which is not vacuous (the inner expression is the predicate); each such usage was spot-checked and asserts a real condition (e.g. `expect(fh.id > 0).to_equal(true)`, `expect(gran > 0).to_equal(true)`).

---

### Pattern 9: Specs where the it-block was removed (git history compare)

**Result:** **DEFERRED** — out of scope (cannot run `git`/`jj` per task rules).

| Approximation done | Result |
|---|---|
| Low-it-count flag (specs with ≤ 3 its) | `arena_as_blob_backend_spec.spl` (3), `bench_harness_smoke_spec.spl` (3), `bench_harness.spl` (3 — undiscovered), `dbfs_hw_passthrough_spec.spl` (2 — in-flux, defer) |

The only true low-it spec under spec discovery is `dbfs_hw_passthrough_spec.spl` (2 its), and `state.md > 4-spec > Spec Corrections Applied` explicitly documents it was *added* with exactly 2 its for AC-6 — not a removed-it case.

**Recommendation:** Phase 7 executor must run `git log -p -S'expect(' -- test/dbfs/` and `git log -p -S' it "' -- test/dbfs/` to cover removed-expect / removed-it cases properly.

---

### Pattern 10: Specs that pass with 0 examples in run output

**Result:** **DEFERRED** — out of scope (cannot run `bin/simple test`).

| Static check | Result |
|---|---|
| Any `*_spec.spl` with 0 it-blocks (would yield "0 examples") | NONE — all 20 spec files have ≥ 2 its |

Static count proves 0 specs would report 0 examples. But verify_plan §5.10 specifically requires runtime confirmation; that is **DEFERRED** to a Phase 7 executor.

---

### Pattern 11: Capability-set tautology

**Result:** 0 hits after applying verify_plan's whitelist.

verify_plan §5.11 grep is: `grep -RnE 'caps\.has\([A-Za-z_]+\)\.to_equal\(true\)' $SCOPE | grep -v 'PosixCompat|COW|Xattr|Acl|LargeFiles'`

| File:Line | Match | Whitelisted? |
|---|---|---|
| `test/dbfs/dbfs_capability_spec.spl:61` | `expect(caps.has(Capability.PosixCompat)).to_equal(true)` | **YES — `PosixCompat` whitelisted** by verify_plan grep |

The `PosixCompat` hit is excluded by the pattern's own definition. Importantly, per `state.md > 4-spec > Spec Corrections Applied`, line 70 was previously a tautology asserting `caps.has(PosixCompat)` inside an `it "does not contain MmapSharedWritable"` block — that was **already fixed** in Phase 4 to `caps.has(Capability.Dedup).to_equal(false)` (line 66).

**0 hits after whitelist.**

---

## 2. Supplementary Stats Table

| File | describes | its | expects | Notes |
|---|---:|---:|---:|---|
| arena_as_blob_backend_spec.spl | 1 | 3 | 13 | helper-delegated expects (Pattern 2 WARN) |
| bench_harness_smoke_spec.spl | 1 | 3 | 3 | **BLOCKING** tautology line 71 |
| bench_harness.spl | 1 | 3 | 3 | undiscovered (no `_spec.spl`); state.md drift |
| dbfs_capability_spec.spl | 3 | 11 | 11 | post-advisor corrected (state.md §4-spec) |
| dbfs_catalog_schema_spec.spl | 6 | 13 | 14 | — |
| dbfs_driver_spec.spl | 4 | 8 | 9 | — |
| dbfs_engine_btree_spec.spl | 4 | 8 | 10 | — |
| dbfs_engine_checkpoint_ring_spec.spl | 3 | 6 | 7 | — |
| dbfs_engine_checkpoint_spec.spl | 4 | 6 | 6 | — |
| dbfs_engine_intent_log_spec.spl | 4 | 6 | 8 | R1 HIGH-risk gap spec |
| dbfs_engine_pager_spec.spl | 4 | 8 | 8 | — |
| dbfs_engine_wal_spec.spl | 3 | 8 | 8 | — |
| dbfs_hw_passthrough_spec.spl | 2 | 2 | 3 | **in-flux (Phase 6) — deferred** |
| dbfs_posix_shim_spec.spl | 5 | 9 | 10 | XXX false-positive line 42 |
| dbfs_recovery_spec.spl | 4 | 7 | 7 | — |
| dbfs_ring_diag_spec.spl | 1 | 6 | 6 | — |
| dbfs_tx_protocol_spec.spl | 3 | 6 | 6 | — |
| fat32_no_regression_spec.spl | 3 | 6 | 7 | — |
| mount_table_dbfs_dispatch_spec.spl | 3 | 7 | 7 | — |
| nvfs_no_regression_spec.spl | 2 | 8 | 14 | R8 evidence |
| power_cut_harness.spl | 0 | 0 | 0 | shared harness module — expected |

Totals: **20 spec files**, **128 it-blocks**, **161 expects**, **1 harness module**.

(`it` count grep used `^\s*it "` strict form; verify_plan §0.2 expected count of 21 `.spl` files matches.)

---

## 3. Cross-Cutting Observations

### 3.1 In-flux file
- `test/dbfs/dbfs_hw_passthrough_spec.spl` — Phase 6 refactor target. **Statically inspected** (39 lines, 2 its, 3 expects, no silent-greens detected as of pre-scan). Once Phase 6 lands its rewrite, Phase 7 should re-run patterns 1-3, 5, 8, 11 against the post-refactor file.

### 3.2 Scope mismatches
- **Pattern 4** (`Result.Ok(0)` stubs in impl) was scanned only in `test/dbfs/`; `src/lib/nogc_sync_mut/db/` is forbidden by my task scope. A Phase 7 executor with broader access must close this.
- **Patterns 9 & 10** require `git`/`jj` and `bin/simple test` execution respectively; both forbidden by task. Static approximations done; runtime confirmation deferred.

### 3.3 Drift between state.md and reality
- `state.md > 4-spec > Spec Corrections Applied` claims `bench_harness.spl` had its `use std.spipe.*` and "all 3 describe/it blocks" stripped. **They were NOT stripped** (lines 259-283 still present, including the `use std.spipe.*` on line 258). Either the file is intentionally kept as runnable-when-explicitly-invoked or the claim is stale. WARN finding under Pattern 3.

### 3.4 Patterns the 11-grep set fundamentally cannot catch
Per advisor pre-write check, the 11 patterns CANNOT detect:
- Expects gated on `if false:`/feature flags hard-set off — none found by static grep `if false`.
- Expects whose RHS calls a stub fixture from `src/lib` returning the same value as LHS — out of test scope.
- Expects validated by `.unwrap()` on a side-effect-free Mock — would require trace inspection.
- Cosmetic `expect(<calc>).to_equal(<same-calc>)` where both sides reduce to the same expression — none found visually.

These are residual blind spots; flag in `state.md > 7-verify` if Phase 7 wants belt-and-suspenders coverage.

---

## 4. Phase 7 Ship-Block List

The following BLOCKING-severity findings MUST be fixed before Phase 8:

| # | File:Line | Pattern | Required action |
|---|---|---|---|
| 1 | `test/dbfs/bench_harness_smoke_spec.spl:71` | 3 (tautology) | Replace `expect(true).to_equal(true)` with an assertion on observable post-state (e.g. `expect(mt.readdir("/data").unwrap().len()).to_equal(0)` after the 10×open/unlink loop). |

**Total ship-blocks: 1.**

If Phase 6 finalizes `dbfs_hw_passthrough_spec.spl` after this scan, re-verify it against patterns 1-3, 5, 8, 11 before Phase 8.

---

## 5. Appendix — Raw Pattern Counts

```
Pattern 1 (skip/pending)               : 0 hits
Pattern 2 (it w/o expect)              : 1 hit  (WARN — helper delegate)
Pattern 3 (tautology)                  : 2 hits (1 BLOCKING + 1 WARN drift)
Pattern 4 (Ok(0) stub)                 : 0 hits in test scope; DEFERRED for src/lib
Pattern 5 (TODO/FIXME/XXX nr expect)   : 1 hit  (NOTE — false-positive payload string)
Pattern 6 (mode=native|smf)            : 0 hits
Pattern 7 (describe w/o it)            : 0 hits in *_spec.spl files
Pattern 8 (vacuous matchers)           : 0 hits
Pattern 9 (removed expects)            : DEFERRED (no git access)
Pattern 10 (0 examples in run)         : DEFERRED (no test runner access); static check 0
Pattern 11 (capability tautology)      : 0 hits after PosixCompat/COW/Xattr/Acl/LargeFiles whitelist
```

---

## 6. Advisor Verdict (pre-write)

Asked: "Did the 11 patterns catch every realistic silent-green? Any spec that's secretly green via inspection-by-eye that the patterns missed?"

Verdict: **Yes for catchable silent-greens; no for runtime-only ones.** Advisor confirmed:
- Pattern 3 BLOCKING/WARN split is correct (`bench_harness_smoke_spec.spl:71` is a real silent-green; `bench_harness.spl:270` is dead code + state.md drift).
- Pattern 11 `PosixCompat` hit is whitelisted by the pattern's own definition — 0 hits after filter, correct.
- Pattern 5 `XXXXXXXXXX` is a false-positive on payload data — correct.
- Patterns 9 + 10 must be flagged DEFERRED, not silently called "0 hits", to keep downstream agents honest.
- Pattern 4 must call out the scope mismatch (`src/lib/nogc_sync_mut/db/` is forbidden in this agent's task).
- Residual blind spots: expects gated on hard-coded feature flags, expects in unreachable branches, mock-fixture self-loops. None observed but the 11 patterns can't prove their absence statically.

Scan ready for Phase 7 executor consumption.
