# SPIPE005 residual: assertion-free SPipe examples

**Date:** 2026-08-01
**Rule:** SPIPE005 — "SPipe example has no real assertion or sanctioned skip"
**Impl:** `src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl`
**Predecessor:** recall fix `2aacc58837ae` (148,634 → 1,790 firings, 98.8% cut)

## Measurement method

A full bootstrap-lint sweep is unaffordable (~1–4 min **per file** × 20,685
test-like files). Numbers below come from a **static re-implementation** of the
rule (`check_spipe_example_bodies` + all its recognizers, including
`is_test_like_file`), validated against the real linter
(`src/compiler_rust/target/bootstrap/simple lint`) on 5 files with **exact
agreement on every one**:

| file | real linter | static model |
|---|---|---|
| `test/01_unit/lib/common/encoding/protobuf_e_spec.spl` | 1 | 1 |
| `test/03_system/feature/usage/minimal_spec.spl` | 1 | 1 |
| `test/03_system/feature/usage/no_paren_calls_spec.spl` | 1 | 1 |
| `test/01_unit/app/tooling/traceability_spec.spl` | 8 | 8 |
| `test/03_system/feature/features/with_statement_basic_spec.spl` | 4 → 0 after fix | 4 → 0 |
| `test/03_system/feature/usage/set_literal_spec.spl` | 13 → 0 after fix | 13 → 0 |
| `test/01_unit/doctest/parser_spec.spl` | 1 → 0 after fix | 1 → 0 |

The prior lane's 1,790 / 196 files was **reproduced exactly**, NEW-ONLY = 0.

## What landed in this pass

### 1. Recall fix — paren-less assertion-family calls (−36 firings, 6 files)

Simple supports paren-less call syntax. `check cleanup_called`,
`check val_ == "hello"` and `fail "Expected Empty"` are **real assertions**
(`check` comes from `std.spec`, `src/lib/nogc_sync_mut/spec.spl:733`), but
`has_assertion_family_call` keys off a following `(` and could not see them.

Added `has_paren_less_assertion_call` as one more disjunct in
`statement_has_direct_assertion` — **additive only, it can never add a firing**.
Verified: 1,790 → 1,754, **NEW-ONLY = 0**.

Precision is preserved by excluding assignment forms: `expected = build(lines)`
has an assertion-family head but binds a variable. 13/13 boundary cases pass,
including `checkpoint foo` → false, `checker x` → false, `val expected = 1` →
false, `expected == build(x)` → true.

### 2. Deleted `protobuf_e_spec.spl` (−2 firings)

`test/{01_unit,unit}/lib/common/encoding/protobuf_e_spec.spl` — a 61-line
fragment that:
- ends mid-`it` at EOF (`it "decodes field_num = 1":` with no body),
- calls `_tag_field1_varint()`, `_fixed32_300()`, `_fixed64_as_field()` which it
  **does not define**, so it was already **RED** (`1 total, 0 passed, 1 failed`),
- has all 8 of its `it` titles as a **strict subset** of the complete sibling
  `protobuf_spec.spl`, which is **45/45 green**.

It is an incomplete bulk-restore artifact from the 2026-06-26 deletion incident
(`doc/08_tracking/bug/encoding_restore_deleted_sources_2026-06-26.md` lists it
among 27 "restored" files). Deleting loses zero coverage. Origin's copy was
verified equally truncated, so this is a forward fix, not a revert.

## Residual: 1,752 firings / 188 files

| category | firings | disposition |
|---|---|---|
| `pass` placeholder | 1,189 | untracked placeholder work — see below |
| **scanner artifact:** multi-line string | 221 | linter defect, see (A) |
| `single non-asserting stmt` | 146 | triage: smoke vs dead scaffolding |
| `setup-only body` | 117 | triage: smoke vs dead scaffolding |
| `pending(...)` placeholder | 37 | deliberate, needs tracking |
| mixed placeholder | 28 | deliberate, needs tracking |
| **scanner artifact:** inside docstring | 11 | linter defect, see (B) |
| empty body | 3 | truncated files, see (C) |

Note the test tree is **duplicated** (`test/01_unit/…` ≡ `test/unit/…`,
`test/03_system/…` ≡ `test/feature/…`, byte-identical in most cases), so unique
sites are roughly half the firing count.

### (A) Body collection truncated by multi-line strings — 221 firings, 36 files

`check_spipe_example_bodies` is line-based and stops collecting body lines at the
first line whose indent ≤ the `it` header indent. A `"""…"""` literal inside an
`it` body whose content is written at column 0 therefore **terminates the body
early**, making a real, asserting example look setup-only.

Example: `src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/test/riscv_common_pmp_spec.spl:25`
collects only `val lowering = """`.

**Fix:** track triple-quote state while scanning so string interiors are never
treated as dedents. Not attempted here — it changes the scanner rather than the
recognizers, and deserves its own verified pass.

### (B) `it` blocks inside module docstrings — 11 firings, 7 files

The scanner does not skip `"""…"""` module docstrings, so a markdown
` ```simple ` fence that *illustrates* `it "…": skip` is linted as a real
example with an empty body. `test/03_system/feature/usage/minimal_spec.spl:18`
is inside the header docstring; the file's actual example (`it "works": check(true)`)
is correctly recognized. Same root cause as (A) — fix both together.

### (C) Remaining empty bodies — 3 firings

All three are **files truncated mid-`it` at EOF**, in tracked bisect scratch:
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_21to50_spec.spl:268`
  — `it "applies case insensitive attribute selectors in fallback pixels":`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_combined_spec.spl:221`
  — `it "applies :first-child selectors in fallback pixels":`
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_pseudo_sel_spec.spl:161`
  — same title

These sit in a family of **13 tracked `tmp_*_spec.spl` files (2,497 lines)** in
that directory whose names (`tmp_21to50`, `tmp_51to56`, `tmp_group_a`,
`tmp_has_debug`, `tmp_combined`) mark them as bisection scratch. Deciding whether
to fold them into `browser_renderer_*_spec.spl` or delete them is a browser-engine
lane call, not a lint call — **not** actioned here. They must not be left
truncated either way.

### `pass` / `pending` placeholders — 1,254 firings, NOT tracked

The 1,189 `pass` firings are concentrated in **43 files (22 unique)**, and are
whole-file skeletons where *every* `it` is `pass`:

| firings | file (also present under `test/unit/…`) |
|---|---|
| 81 | `test/01_unit/compiler/semantics/gc_safety_spec.spl` |
| 61 | `test/01_unit/app/interpreter/ast_convert_expr_spec.spl` |
| 61 | `test/01_unit/app/test_runner/quickcheck_spec.spl` |
| 61 | `test/01_unit/compiler/native/simd_check_spec.spl` |

`doc/02_requirements/feature/pending_feature.md` **does not exist**, so none of
this is tracked as pending work. Per repo rule (*never convert TODO to NOTE —
implement or delete*), each of these 22 files needs an explicit decision:
implement the skeleton, or delete it. A green `pass` skeleton is a
false-confidence generator: `gc_safety_spec.spl` reports 81 passing examples
while asserting nothing about GC safety.

**Recommended next action, highest value first:**
1. Fix scanner (A)+(B) — removes 232 firings that are not real defects.
2. Decide the 22 `pass`-skeleton files (implement or delete) — 1,189 firings.
3. Repair the 3 truncated `tmp_*` browser-engine specs.
4. Triage the 263 single-stmt / setup-only bodies; the `print "… implementation
   pending"` sub-cluster (58 firings, e.g. `test/01_unit/app/tooling/test_db_concurrency_spec.spl`)
   is placeholder work mislabelled as a passing test.

## Category 0 — fake-pass `pending_reason` tautology (INVISIBLE to SPIPE005)

Worse than a bare `pass`, because `pass` is at least honest about asserting
nothing. The whole live body of the example is:

```
describe "Advanced":
    it "skipped":
        val pending_reason = "pre-existing test failures - functions/imports not available"
        expect pending_reason.len() > 0
```

It asserts only that a locally-constructed literal is non-empty, so it can never
fail, and it reads in the results as a passing example. SPIPE005 does not fire
because `expect <expr>` is a real assertion form.

**Two corrections to the reported scope:**

1. The reported grep `expect(pending_reason.len() > 0).to_equal(true)` matches
   **0 files**. The form actually in the tree is the **paren-less**
   `expect pending_reason.len() > 0`.
2. `pending_reason.len() > 0` matches **461 files** under `test/`, not 16 —
   but **every one is a generated `.spipe_matchers_*` file**, and only **16 of
   those are git-tracked**. The other 445 are untracked local generation
   artifacts (absent from a clean checkout, but they do pollute local lint and
   test sweeps). 16 is the correct *tracked* count.

Every one of the 16 had exactly **4 live lines** (the fake-pass) with the entire
original spec commented out below it, and defined **zero** `fn`/`me`/`class`, so
nothing depended on them. **All 16 deleted:**

- 3 in `test/01_unit/lib/database/` — `core_interner_table`, `database_atomic`,
  `database_e2e`. Subject live; the real sibling spec carries the coverage.
- 9 with a live real sibling — `compiler/async/async_pipeline`,
  `compiler/backend/{backend_orchestration,native_backend}`,
  `compiler/hir/{hir_async,hir_async_errors,hir_async_integration}`,
  `compiler/mono/mono_cache_efficiency`, `compiler/semantics/borrow_check`,
  `compiler_core/bidir_type_check`.
- 4 **orphans with no sibling at all** —
  `compiler/type_inference/{bidirectional,expr_inference,module_check,stmt_check}`.
  Only the directories remain; the spec files they shadowed are gone. This is the
  same dead type-inference cluster as `d48bc04ab35b`; those four were the
  remainder.

### Root cause: `.spipe_matchers_*` are transient artifacts that got committed

Deleting these files is **not by itself a durable fix**. They are temp rewrites
the test runner emits next to each spec at execution time —
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:420`:

```
val tmp = dir + ".spipe_matchers_" + base
file_write(tmp, joined)
```

Running any spec regenerates its neighbour verbatim. This was observed directly:
the three `test/01_unit/lib/database/` files were deleted, a spec was run to
verify, and they reappeared at 15:05 with the identical 4-line fake-pass body —
and were therefore re-added by the first landing of this change.

They are **not gitignored**, and **101 of them are tracked**. That is the real
defect: a per-run build artifact is under version control, which is how a
commented-out spec with a fake-pass body became durable repo content in the first
place. **Recommended fix (not done here, it is a test-runner-lane change):** add
`.spipe_matchers_*` to `.gitignore` and untrack all 101 in one pass, or have the
runner emit them under `build/` instead of beside the spec.

### Follow-on finding: the "real siblings" are source-text greps

Deleting the fake-pass files does **not** restore the coverage they implied. The
database siblings that supposedly carry it are themselves ~96% commented out and
what remains only greps the implementation *as text*:

```
fn database_core_source() -> text:
    rt_file_read_text("src/lib/nogc_sync_mut/database/core.spl") ?? ""
it "keeps string interner and row primitives available":
    expect(source).to_contain("class StringInterner:")
```

`core_interner_table_spec.spl` is 855 lines with **3 live `it`s** (72 commented
out); `database_atomic_spec.spl` 236 lines / 2 live; `database_e2e_spec.spl` 480
lines / 4 live. None instantiate `StringInterner` or `SdnTable`. They pass if the
substring is present and would keep passing if the method body were emptied —
the same failure mode as the WASM spec that never instantiated its class. Filed
here; restoring real database coverage is a database-lane task.

**Not proposed:** extending SPIPE005 to flag this class. It requires reasoning
about whether an asserted expression is data-dependent on the code under test,
which the current line-based scanner cannot do; a naive "literal-derived subject"
rule would need its own before/after measurement and is a separate change.

### Verification note

`test/01_unit/lib/database/database_atomic_spec.spl` does not currently run —
but the failure is **pre-existing and unrelated**: `compile failed: parse: in
"src/compiler/20.hir/hir_lowering/types.spl": Unexpected token: expected
expression, found TripleLt`. That is the compiler failing to parse its own HIR
source, not an effect of these deletions. Deleting a file that defines nothing
cannot change it.

## Rule integrity

No firing was silenced by weakening the rule. The only recognizer added matches a
genuine assertion idiom (paren-less `check`/`fail`), was proven additive
(NEW-ONLY = 0) and precision-tested against assignment lookalikes. No `pass` was
added to any spec to suppress a finding.
