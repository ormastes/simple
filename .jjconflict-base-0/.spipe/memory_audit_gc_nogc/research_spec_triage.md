# GC/NoGC/Memory Spec Triage Audit

**Date:** 2026-06-11  
**Mode:** interpreter (default)  
**Timeout per spec:** 120s  

---

## Triage Table

| # | Spec File | Status | it blocks (file) | it blocks (reported) | Hollowness Flags | Verdict |
|---|-----------|--------|-------------------|----------------------|------------------|---------|
| 1 | `test/01_unit/compiler/semantics/gc_safety_spec.spl` | **PASS** | 81 | 81 | none | Genuine pass. Real assertions covering escape state, allocation sites, root tracking, write barriers. |
| 2 | `test/01_unit/compiler/semantics/gc_boundary_enforcement_spec.spl` | **PASS** | 30 | 30 | 8× `to_equal(true)` — but in meaningful predicate checks e.g. `is_nogc_family("nogc_sync_mut")` | Genuine pass. The `to_equal(true/false)` calls are predicate assertions, not tautologies. |
| 3 | `test/01_unit/compiler/semantics/gc_boundary_check_spec.spl` | **FAIL** | 9 | 9 (7 pass, 2 fail) | 1× `to_equal(true)` (meaningful) | **Product bug** — see failure detail below. |
| 4 | `test/01_unit/compiler/semantics/alloc_checker_spec.spl` | **HOLLOW** | 13 | 1 | All 12 real `it` blocks commented out; only "skipped" block active with `expect(pending_reason.len()).to_be_greater_than(0)` | Hollow pass. The single active test just checks a non-empty string literal. No alloc_checker logic exercised. |
| 5 | `test/01_unit/compiler/semantics/alloc_inference_spec.spl` | **HOLLOW** | 24 | 1 | All 23 real `it` blocks commented out; only "skipped" block active with `expect(pending_reason.len()).to_be_greater_than(0)` | Hollow pass. Comment in spec says compiler module imports cause OOM in interpreter test runner (~4GB RSS). No inference logic exercised. |
| 6 | `test/01_unit/compiler/semantics/gc_strategy_naming_spec.spl` | **PASS** | 2 | 2 | 1× `to_equal(true)` in meaningful `starts_with()` check | Genuine pass. Uses `rt_process_run` + `rg` to grep source for `enum GcMode:` / `enum GcStrategy:` — real regression guards. |
| 7 | `test/01_unit/compiler/parser/alloc_attr_spec.spl` | **PASS** | 10 | 10 | none | Genuine pass. |
| 8 | `test/01_unit/compiler/parser/new_alloc_spec.spl` | **PASS** | 9 | 9 | none | Genuine pass. |
| 9 | `test/00_formal_verification/compiler/memory_capabilities_spec.spl` | **FAIL** | 6 | 6 (4 pass, 2 fail) | 8× `to_equal(true/false)` — all meaningful | **Product bug** — see failure detail below. |

### Leak Specs (`find test -name '*leak*spec.spl'`)

| # | Spec File | Status | it blocks (file) | it blocks (reported) | Hollowness Flags | Verdict |
|---|-----------|--------|-------------------|----------------------|------------------|---------|
| 10 | `test/01_unit/compiler/loader/leak_check_spec.spl` | **PASS** | 19 | 19 | 8× `to_equal(true)` — all meaningful mock-registry checks | Genuine pass. Tests SMF module registry, JIT symbol origin tracking, eviction. |
| 11 | `test/01_unit/memleak/baseline_memleak_spec.spl` | **PASS** | 3 | 3 | none | Genuine pass. |
| 12 | `test/01_unit/memleak/iteration2_memleak_spec.spl` | **PASS** | 2 | 2 | none | Genuine pass. |
| 13 | `test/01_unit/memleak/iteration3_memleak_spec.spl` | **PASS** | 2 | 2 | none | Genuine pass. |
| 14 | `test/01_unit/memleak/c_runtime_leak_spec.spl` | **PASS** | 2 | 2 | none | Genuine pass. |

---

## Failure Details

### FAIL #3 — `gc_boundary_check_spec.spl` (7 pass, 2 fail)

**Failing tests (from test_result.md tracking):**
1. `"does not warn when gc async imports no-gc"` — spec calls `check_gc_boundary_imports("std.gc_async_mut.gpu", ["std.nogc_sync_mut.fs"])` and expects `warnings.len() == 0`.
2. `"rejects lower runtime layers importing hosted adapters"` — spec calls `check_runtime_family_import_violations("std.nogc_async_mut.actor", ["std.nogc_sync_mut.io"])` and expects `violations.len() == 1` with `reason == "higher_layer_runtime_family"`.

**Root cause (product bug):**  
The implementation in `src/compiler/35.semantics/gc_boundary_check.spl` has Rule 3 added (symmetric): `if source.gc_mode == "gc" and imported.gc_mode == "nogc": return "gc_imports_nogc_family"` which triggers a warning for GC→noGC imports. The spec was written expecting gc_async_mut → nogc_sync_mut to be allowed (no warning). The rule was added after the spec was written, making the spec's expectation stale. This is a **product behaviour change** that was not reflected in the spec.  

For test 2: `nogc_async_mut` has rank 2, `nogc_sync_mut` has rank 3. Since `imported.rank (3) > source.rank (2)`, `import_violation_reason` returns `"higher_layer_runtime_family"`. The `check_runtime_family_import_violations` fn should return this violation. Likely a separate bug: this function is exported but `check_gc_boundary_check_spec` imports it — if `check_runtime_family_import_violations` was added to the export list only later, or has a different codepath. Needs runtime trace to confirm.

**Triage: Product bug** — the gc-imports-nogc symmetric rule (Rule 3) was added to the implementation but the spec contract was not updated. The spec test "does not warn when gc async imports no-gc" reflects the original intent (one-directional enforcement). The second failure may be a separate product bug in the manifest-backed violations path.

---

### FAIL #9 — `memory_capabilities_spec.spl` (4 pass, 2 fail)

**Failing tests (from test_result.md tracking):**
1. `"builds Lean syntax"` (CapType context)
2. `"stores and consumes references"` (RefEnv context)

**Root cause analysis:**

**"builds Lean syntax":** `CapType.to_lean()` in `src/compiler_rust/lib/std/src/verification/models/memory_capabilities.spl` uses string interpolation:  
`"CapType.mk \"{self.type_name}\" RefCapability.{cap_lean}"`  
The test expects `to_equal("CapType.mk \"Int\" RefCapability.Shared")`. The issue is how the interpreter renders `\"` inside a string interpolation — the backslash-escaped quote in the interpolated string may produce a literal `"` character, but the expected value in the test also uses `\"` which in Simple means a literal double-quote. Both sides should agree. However the actual output may differ depending on interpolation scoping.  
**Triage: Product bug** — likely an interpreter bug in string interpolation with escaped quotes, or a mismatch in how `\"` is handled inside `"..."` vs as a value in `to_equal("...")`.

**"stores and consumes references":** `RefEnv.consume("x")` calls `ref.consume()` on a dict-lookup value. The `me consume()` method mutates `self.is_consumed = true`. However, `self.refs.get(name)` returns a copy of the `Reference` value (dict returns by value in Simple), so `ref.consume()` mutates the copy, not the dict entry. `is_available("x")` then checks the original (unconsumed) dict entry and returns `true` instead of `false`.  
**Triage: Product bug** — this is the documented [cross-module mutation loss] / arrays-are-value-types issue. `Dict.get()` returns a copy; mutating via `me` method on the copy doesn't update the dict. The implementation at lines 255-265 is structurally broken for this reason.

---

## Summary

| Status | Count | Specs |
|--------|-------|-------|
| PASS (genuine) | 9 | gc_safety, gc_boundary_enforcement, gc_strategy_naming, alloc_attr, new_alloc, leak_check, baseline_memleak, iteration2_memleak, iteration3_memleak, c_runtime_leak |
| FAIL | 2 | gc_boundary_check (2 tests), memory_capabilities (2 tests) |
| HOLLOW | 2 | alloc_checker (12/13 it blocks commented out), alloc_inference (23/24 it blocks commented out) |
| TIMEOUT | 0 | — |

**Hollow specs note:** Both hollow specs have a single "skipped" sentinel block that passes trivially (`expect(non_empty_string.len()).to_be_greater_than(0)`). They are not false-greens in the dangerous sense — they explicitly document why they're skipped — but they provide zero coverage of their named feature areas.

**Most important findings:**
1. `alloc_checker_spec` and `alloc_inference_spec` cover **zero** production logic — 12 and 23 real tests respectively are dead code. `alloc_inference` is blocked by OOM (~4GB RSS on full compiler frontend import).
2. `gc_boundary_check_spec` has 2 failures: the symmetric `gc_imports_nogc_family` rule was added to the product without updating the spec's "should not warn" contract.
3. `memory_capabilities_spec` "stores and consumes references" failure is a value-type copy bug — `Dict.get()` returns a copy, so `me consume()` on the copy doesn't update the stored entry. This is a known interpreter limitation.
