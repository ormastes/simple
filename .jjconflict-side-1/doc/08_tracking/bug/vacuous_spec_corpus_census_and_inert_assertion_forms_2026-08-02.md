# Vacuous spec corpus census, proved inert assertion forms, and remainder backlog

- **Date:** 2026-08-02
- **Status:** OPEN — 6 of 5,095 vacuity-bearing files repaired; remainder listed below
- **Scope:** `test/**/*_spec.spl` (tracked). Vendored source excluded per CLAUDE.md
  owned-code scope.
- **First repair landed:** `c38e72fcb5e275b9e51a765f6d9d4ed726514bcd`

A vacuous spec reports green while proving nothing. This doc records an anchored
census of the whole spec corpus, the assertion forms that were empirically shown
to be inert (and, just as importantly, the ones that were **not**), the measured
false-positive rate of the scan itself, and the per-file remainder list.

Every count below is labelled PROVED or INFERRED. Counts and extrapolations are
kept separate.

---

## 1. Both previously recorded backlog figures are REFUTED

| Claim | Recorded | Measured | Verdict |
|---|---|---|---|
| File-level vacuous specs | ~791 | **5,095** unique files | REFUTED, 6.4x under |
| Assertion-level (SPIPE005) | ~188 | not reproducible as stated | REFUTED |

Both recorded numbers were inferred from an earlier sweep and never verified.
The figures in this doc come from an anchored scan with the predicate stated in
section 4, run against a clean checkout of the origin tip.

---

## 2. Census — PROVED

Scanned **18,735** tracked `*_spec.spl`. The corpus carries twin trees
(`test/01_unit/**` vs `test/unit/**`, `test/03_system/**` vs `test/system/**`)
whose contents are byte-identical, so raw file counts double-count. After
collapsing twins: **12,804 unique spec files, 146,688 unique examples.**

| Example class | Count | Share |
|---|---|---|
| LIVE | 123,588 | 84.3% |
| ONLY_TAUT | 19,900 | 13.6% |
| WEAKENED | 1,061 | 0.7% |
| NO_ASSERT | 979 | 0.7% |
| ONLY_INERT | 592 | 0.4% |
| PASS_ONLY | 568 | 0.4% |

- **Fully vacuous: 22,039 examples (15.0%) across 5,095 unique files.**
- **Partially weakened: 1,061 examples** (carry a live assertion *and* a dead one).
- Files whose `describe` block contains zero executable examples: **2,704**.
- Tier split of the 5,095 vacuity-bearing files: HIGH 294, MED 737, LOW 4,064.

Fully vacuous and partially weakened are tracked separately on purpose: the
first proves nothing, the second still proves something and only needs its dead
assertion revived.

---

## 3. Assertion forms — PROVED by direct probe

Each form below was written into a minimal spec asserting a **false**
proposition and run with `src/compiler_rust/target/debug/simple run`. A form
that exits 0 on a false proposition is inert.

### 3.1 INERT — reports green on a false condition

| Form | Probe | Result | Corpus lines |
|---|---|---|---|
| bare statement `assert` | `assert 1 == 2` | GREEN | 273 |
| matcher-less `expect` | `expect(false)` | GREEN | 5,148 |
| **space instead of dot** | `expect(1) to_equal(2)` | GREEN | 1,142 |

The third is newly identified by this lane and was in no prior backlog. Writing
a space where a `.` belongs silently discards the matcher. All 1,142 occurrences
sat in six RISC-V Vector encoder specs; they are fixed in the commit above.

### 3.2 LIVE — hypotheses REFUTED

These were suspected inert and are not. Recording them so nobody re-opens them:

| Form | Probe | Result |
|---|---|---|
| statement-form `expect` | `expect 1 == 2` | RED (live) |
| naked matcher, no `expect` | `v().to_equal(2)` | RED (live) |
| `.to eq(...)` space form | `expect(1).to eq(2)` | RED (live) |
| `.to(eq(...))` form | `expect(1).to(eq(2))` | RED (live) |

Statement-form `expect` matters most: an intermediate version of this scan
wrongly classified it inert, which would have condemned **26,363** healthy
assertion lines. It is live.

---

## 4. The dominant mechanism was in no brief: literal-only auto-generated specs

The largest single class of vacuity here is **not** any of the known mechanisms.
It is auto-generated "coverage" specs whose examples compute only on literals:

```
it "type checking":
    check(1 + 1 == 2)

it "nested if - true/true":
    if true:
        check(true)
    else:
        check(false)
```

`check` is a local helper wrapping a real `expect(...).to_equal(...)`, so the
assertion **is** live — it simply asserts a tautology about the language's own
literals. The example never names any imported or shipped symbol, so no change
to any implementation can turn it red. It reports green forever and inflates
coverage while testing nothing. The example name (`"type checking"`,
`"code generation"`) claims otherwise.

- **19,900 examples classify ONLY_TAUT.**
- **81,650 examples reference zero symbols from outside the spec file** — a
  strictly structural property: such an example cannot observe shipped code.
- File families: `auto_coverage_N_spec.spl`, `branch_coverage_N_spec.spl`,
  `spec_deep_N_spec.spl`, and the `test/**/std/{improved,deep,complete}/` trees.

These should be deleted or rewritten against real APIs, not "fixed" in place.

### Predicate used (reproduce without the scanner)

The scan is not committed (repo requires `.spl`/`.shs`). It is reproducible from
this description:

1. Split each file into `it "..."` / `scenario "..."` blocks by indentation: a
   block ends at the first non-blank line whose indent is `<=` the `it` line's.
2. Collect `use` targets, ignoring `std.spec`, as the **imported** name set.
   Collect top-level `fn`/`class`/`struct`/`enum` names defined in the spec file;
   a top-level `fn` whose body contains an assertion is an **assertion helper**.
3. Per line classify the assertion: `expect(..)` + chained `.to_*`/`.not_to*`/
   `.should_*`, or `assert_true/false/eq/...(..)`, or statement-form `expect X`
   → LIVE. `expect(..)` with no matcher, `assert X`, and `expect(..) to_*(..)`
   with whitespace instead of `.` → INERT. A call to an assertion helper takes
   the class of its argument expression.
4. An assertion whose operands are literals only (`true`, `false`, numeric, string
   literals combined with operators), or `expect(x).to_equal(x)` on the same
   token, is TAUT.
5. Class the example: no assertions → NO_ASSERT; body only `pass`/comments →
   PASS_ONLY; all assertions inert → ONLY_INERT; all live assertions tautological
   → ONLY_TAUT; live plus inert/taut → WEAKENED; else LIVE.
6. Orthogonal flag: the example references no imported symbol and no non-helper
   top-level name → cannot observe shipped code.

---

## 5. False-positive rate OF THIS SCAN — measured, not estimated

Twelve flagged examples were reviewed by hand:

| Class | Sampled | False positives | Rate | Confidence |
|---|---|---|---|---|
| ONLY_INERT | 6 | 2 | 33% | medium |
| NO_ASSERT | 6 | 3 | 50% | **low** |
| ONLY_TAUT / PASS_ONLY | — | — | — | high |

**Do not trust the NO_ASSERT figure (979) blindly.** Its errors have one
dominant cause: triple-quoted (`"""`) multi-line strings defeat the
indentation-based block extraction in step 1, so the scanner loses the rest of
the example — including its assertions — and reports the example as
assertion-free. Any file using heredocs is suspect. `ONLY_INERT`'s residual
errors came from matcher chains split across lines.

`ONLY_TAUT` and `PASS_ONLY` do not depend on block-end detection in the same way
and are the two classes safe to act on without re-review.

---

## 6. Truth reveals from the first repair: 2

De-vacuifying the RVV encoder specs made two assertions fail that had never been
evaluated. **In both cases the golden in the spec was wrong and the shipped
implementation was correct.** Correct values were derived by hand from the
encoding formula documented in each file header and cross-validated against the
`vadd.vv` case, which passes:

```
word = funct6*2^26 + vm*2^25 + vs2*2^20 + vs1*2^15 + funct3*2^12 + vd*2^7 + 87
```

1. `emit_vmul_vv(1, 2, 3)` — golden said word `0x962120D7`, byte[1] `0x20`.
   Correct word is `0x9621A0D7`, byte[1] `0xA0`. The golden dropped bit 15, the
   low bit of `vs1=3`.
2. `emit_vsha2cl_vv(1, 2, 3)` — golden asserted byte[2] `0xA0`. The word
   `0xBE21A0D7` was right but byte[2] of it little-endian is `0x21`, not `0xA0`;
   the golden read the wrong byte index.

Neither was weakened, skipped, or baselined. Both goldens were corrected to the
independently derived values.

**Resolving a test-vs-implementation disagreement by re-deriving the expected
value from the specification, and validating the derivation against a case that
already passes, is the standard this lane holds.** Never edit a golden to
whatever the implementation happens to emit.

---

## 7. Non-vacuity proof obligation

A repair that cannot be made to fail is still vacuous. Every repair in this lane
must show the full four-cell matrix, sabotaging the **shipped** implementation —
never a shim or a local copy. For `c38e72fcb5e`, sabotaging
`src/compiler/70.backend/backend/native/encode_rvv_int.spl` (`vmul` funct6
`0x25` -> `0x26`):

| | clean impl | sabotaged impl |
|---|---|---|
| **pristine (vacuous) spec** | GREEN | **GREEN, 0 failures** — the vacuity |
| **repaired spec** | GREEN | **RED, 3 of 22 examples failed** |

Control spec `rvv_widen_spec.spl` (implementation untouched) stayed GREEN
throughout, and restoring the sabotage returned the repaired spec to GREEN.

The bottom-left cell is the proof of the defect; the top-right cell is the proof
that the spec had been blind to it.

---

## 8. Separate finding, NOT acted on: the corpus is ~46% duplicated

`test/01_unit/**` and `test/unit/**` are twin trees, as are `test/03_system/**`
and `test/system/**`. For all 12 files touched by the first repair the twins were
byte-identical (`cmp` clean), so every fix must be applied twice and every count
taken from raw file listings is inflated roughly 2x.

18,735 raw spec files collapse to 12,804 unique.

This is a structural problem with its own remedy and its own risk, independent
of vacuity. **A decision is needed on whether these trees should be
deduplicated, and by whom.** This lane deliberately did not act on it and
mirrored its changes into both trees instead.

---

## 9. Remainder — per-file classification

6 of 5,095 vacuity-bearing unique files are repaired. The rest are listed below,
tier first, then by vacuous-example count descending.

Columns: `vac/tot` fully-vacuous examples over total examples in the file;
`weak` partially weakened; `zero` file has a `describe` but no examples;
then the per-class split `PASS`(only `pass`) / `NOASS`(no assertion) /
`INERT`(all assertions inert) / `TAUT`(all live assertions tautological).

Highest-value next targets, both HIGH tier and both single-mechanism:

- `01_unit/compiler/semantics/gc_safety_spec.spl` — 81/81 PASS_ONLY; every
  example body is commented-out intent plus `pass`.
- `01_unit/compiler/type_checker/type_inference_v2_spec.spl` — 70/70 ONLY_TAUT;
  every body is `expect true  # Placeholder until module import works`.


## HIGH tier — complete (294 files)

```
vac/tot  weak zero  PASS NOASS INERT TAUT  path
  81/  81    0    0    81     0     0    0  01_unit/compiler/semantics/gc_safety_spec.spl
  70/  70    0    0     0     0     0   70  01_unit/compiler/type_checker/type_inference_v2_spec.spl
  70/  70    0    0     0     0     0   70  01_unit/lib/std/type_checker/type_inference_v2_spec.spl
  29/  40    0    0     0     0     0   29  feature/usage/capability_system_spec.spl
  26/  26    0    0     0    26     0    0  01_unit/app/office/sheets/formula_forecast_pivot_spec.spl
  24/  40    1    0     0     0     0   24  03_system/feature/usage/capability_system_spec.spl
  21/  53    0    0     0     0    21    0  01_unit/app/office/sheets/number_format_spec.spl
  17/  17    0    0    17     0     0    0  01_unit/lib/nogc_async_mut/io/async_file_spec.spl
  15/  15    0    0     0    15     0    0  03_system/feature/usage/gc_managed_default_spec.spl
  15/  15    0    0     0    15     0    0  feature/usage/gc_managed_default_spec.spl
  14/  14    0    0     0    14     0    0  01_unit/lib/nogc_async_mut/io/async_tcp_spec.spl
  14/  22    0    0     0     0     0   14  03_system/feature/compiler/bootstrap_system_spec.spl
  14/  14    0    0     0     0     0   14  03_system/feature/usage/sandboxing_spec.spl
  14/  14    0    0     0     0     0   14  feature/usage/sandboxing_spec.spl
  12/  32    0    0     0    12     0    0  01_unit/app/io/jit_ffi_spec.spl
  12/  14    0    0    12     0     0    0  01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl
  11/  11    0    0     0    11     0    0  01_unit/lib/crypto/ml_kem_1024_kat_spec.spl
  11/  11    0    0     0    11     0    0  01_unit/lib/crypto/ml_kem_512_kat_spec.spl
  11/  11    0    0     0     0     0   11  01_unit/lib/nogc_async_mut/arc_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/codegen_edge_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/codegen_error_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/codegen_integration_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/codegen_unit_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/crypto_edge_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/crypto_error_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/crypto_integration_spec.spl
  11/  41    0    0     0     0     0   11  01_unit/std/improved/crypto_unit_spec.spl
   9/  24   14    0     0     7     2    0  03_system/security/simple_web_browser_engine_security_spec.spl
   8/  16    0    0     0     8     0    0  01_unit/app/tooling/traceability_spec.spl
   8/  11    0    0     0     8     0    0  02_integration/lib/std/screenshot/screenshot_ffi_spec.spl
   7/  28    1    0     0     0     0    7  03_system/feature/features/ffi_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/feature/features/gc_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/feature/features/memory_system_spec.spl
   7/  28    1    0     0     0     0    7  system/features/ffi_system_spec.spl
   7/  28    1    0     0     0     0    7  system/features/gc_system_spec.spl
   7/  28    1    0     0     0     0    7  system/features/memory_system_spec.spl
   6/  10    0    0     0     0     0    6  01_unit/compiler/codegen/codegen_coverage_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_codegen_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_codegen_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_codegen_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/borrow_check_lifetime_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/borrow_check_lifetime_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/borrow_check_lifetime_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/borrow_check_region_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/borrow_check_region_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/borrow_check_region_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_class_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_class_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_class_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_expr_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_expr_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_expr_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_fn_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_fn_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_fn_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_stmt_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_stmt_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/codegen_stmt_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_lowering_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_lowering_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_lowering_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_dynamic_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_dynamic_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_dynamic_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_static_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_static_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_static_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_symbol_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_symbol_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/linker_symbol_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_lowering_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_lowering_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_lowering_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_expr_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_expr_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_expr_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_pattern_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_pattern_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_pattern_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_stmt_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_stmt_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_check_stmt_3_spec.spl
   6/  28    1    0     0     0     0    6  03_system/compiler/type_checker_system_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/compiler_c_codegen_complete_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/cuda_memory_integration_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/cuda_memory_unit_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_alloc_integration_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_alloc_unit_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_arena_integration_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_arena_unit_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_gc_integration_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_gc_unit_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_pool_integration_spec.spl
   5/  15    0    0     0     0     0    5  01_unit/lib/extended/memory_pool_unit_spec.spl
   5/  61    0    0     0     0     5    0  01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.spl
   5/   5    0    0     5     0     0    0  01_unit/lib/nogc_async_mut/io/async_udp_spec.spl
   4/  12    0    0     0     0     0    4  01_unit/app/extended/verify_basic_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/borrow_check_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/borrow_check_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/borrow_check_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/borrow_check_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/borrow_check_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/codegen_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/codegen_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/codegen_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/codegen_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/codegen_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/linker_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/linker_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/linker_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/linker_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/linker_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/lowering_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/lowering_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/lowering_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/lowering_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/lowering_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_check_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_check_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_check_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_check_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_check_5_complete_spec.spl
   4/  90    0    0     0     0     0    4  01_unit/lib/nogc_async_mut/concurrent_providers_spec.spl
   4/  40    0    0     0     0     0    4  01_unit/lib/nogc_async_mut/concurrent_wrappers_spec.spl
   4/  15    0    0     0     0     4    0  01_unit/lib/nogc_sync_mut/http/auth/basic_spec.spl
   4/   4    0    0     0     4     0    0  01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl
   4/  22    0    0     0     4     0    0  03_system/feature/features/baremetal/memory_layout_spec.spl
   4/   4    0    0     0     4     0    0  03_system/feature/usage/borrowing_spec.spl
   4/   4    0    0     0     4     0    0  feature/usage/borrowing_spec.spl
   4/  22    0    0     0     4     0    0  system/features/baremetal/memory_layout_spec.spl
   3/   3    0    0     0     0     3    0  01_unit/compiler/codegen/native_cross_module_abi_spec.spl
   3/   8    3    0     0     0     3    0  01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_cache_policy_spec.spl
   3/   4    0    0     0     3     0    0  01_unit/lib/nogc_async_mut/ml/autograd_spec.spl
   3/   5    0    0     0     3     0    0  01_unit/lib/nogc_async_mut/ml/linalg_spec.spl
   3/   4    0    0     0     3     0    0  01_unit/os/kernel/ipc/sandbox_lowering_install_spec.spl
   3/   3    0    0     0     0     0    3  03_system/feature/usage/mutability_control_spec.spl
   3/   3    0    0     0     0     0    3  feature/usage/mutability_control_spec.spl
   2/   2    0    0     0     0     2    0  01_unit/compiler/codegen/baremetal_cross_module_val_spec.spl
   2/  11    1    0     0     0     2    0  01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl
   2/  13    3    0     0     0     2    0  01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation_gradient_spec.spl
   2/  33    0    0     0     0     0    2  01_unit/lib/nogc_async_mut/concurrent_spec.spl
   2/   9    0    0     0     0     2    0  01_unit/memleak/fork_alloc_tracking_spec.spl
   2/   6    0    0     0     2     0    0  01_unit/os/crypto/rsa_contract_parity_spec.spl
   2/   4    0    0     0     2     0    0  01_unit/os/kernel/security/sandbox_boot_apply_spec.spl
   1/   6    0    0     0     0     1    0  01_unit/app/office/sheets/access_controller_spec.spl
   1/   1    0    0     0     0     0    1  01_unit/app/tooling/refactor_lowering_spec.spl
   1/  24    0    0     0     0     0    1  01_unit/app/tooling/sandbox_spec.spl
   1/  15    0    0     0     0     1    0  01_unit/compiler/linker/native_link_hardening_spec.spl
   1/  13    0    0     0     0     1    0  01_unit/lib/crypto/chacha20_poly1305_spec.spl
   1/  20    0    0     0     0     0    1  01_unit/lib/ffi/ffi_basics_spec.spl
   1/  22    0    0     0     0     0    1  01_unit/lib/gc_async_mut/gpu_context_spec.spl
   1/  15    0    0     0     1     0    0  01_unit/lib/gc_async_mut/gpu_runtime_spec.spl
   1/   8    5    0     0     0     1    0  01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl
   1/ 113    6    0     0     0     1    0  01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl
   1/  27    0    0     1     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_21to50_spec.spl
   1/  21    0    0     1     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_combined_spec.spl
   1/  12    0    0     1     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_pseudo_sel_spec.spl
   1/  34    0    0     0     0     1    0  01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl
   1/   2    0    0     0     1     0    0  01_unit/lib/gc_async_mut/processing/fault_injection_spec.spl
   1/   3    0    0     0     0     0    1  01_unit/lib/nogc_async_mut/actor_body_spec.spl
   1/   1    0    0     0     1     0    0  01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl
   1/   1    0    0     0     0     0    1  01_unit/lib/nogc_async_mut/game3d/test_audio_spec.spl
   1/   1    0    0     0     1     0    0  01_unit/lib/nogc_async_mut/ml/engine_spec.spl
   1/   3    0    0     0     0     1    0  01_unit/lib/nogc_sync_mut/spec_bool_expect_spec.spl
   1/   5    0    0     0     0     1    0  01_unit/lib/security/.spipe_wrapped_entry_remote_security_quorum_spec.spl
   1/  13    0    0     0     0     1    0  01_unit/memleak/thread_alloc_tracking_spec.spl
   1/   3    0    0     0     0     0    1  02_integration/app/loader_exec_memory_spec.spl
   1/   2    0    0     0     0     1    0  02_integration/compiler/phase2_low_memory_source_reclaim_probe_spec.spl
   1/  10    0    0     0     0     0    1  02_integration/e2e/type_check_inference_integration_1_spec.spl
   1/   1    0    0     0     1     0    0  03_system/security/browser_hsts_history_chrome_spec.spl
   1/   1    0    0     0     1     0    0  03_system/security/browser_renderer_attachment_boundary_spec.spl
   1/   1    0    0     0     1     0    0  03_system/security/browser_renderer_command_capability_spec.spl
   0/  26    1    0     0     0     0    0  01_unit/app/office/word_edit_ops_spec.spl
   0/   3    1    0     0     0     0    0  01_unit/app/office/sheets/formula_text_fmt_spec.spl
   0/  21    1    0     0     0     0    0  01_unit/app/ui/web_auth_hardening_spec.spl
   0/   5    1    0     0     0     0    0  01_unit/compiler/bootstrap/ast_native_arena_spec.spl
   0/   0    0    1     0     0     0    0  01_unit/lib/common/crypto/sha3_kat_spec.spl
   0/   9    9    0     0     0     0    0  01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl
   0/   1    1    0     0     0     0    0  01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.spl
   0/  43   12    0     0     0     0    0  01_unit/lib/common/web/browser_session_security_boundary_spec.spl
   0/  27    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl
   0/ 130    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl
   0/  47    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl
   0/   3    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl
   0/   1    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.spl
   0/   2    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl
   0/   2    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_module_split_spec.spl
   0/  10    3    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_input_overlay_spec.spl
   0/  11    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/style_animation_spec.spl
   0/   7    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl
   0/  52    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_50plus_spec.spl
   0/  26    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl
   0/  23    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl
   0/   6    1    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl
   0/   8    6    0     0     0     0    0  01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl
   0/   5    1    0     0     0     0    0  01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl
   0/   5    1    0     0     0     0    0  01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl
   0/   1    1    0     0     0     0    0  01_unit/lib/nogc_sync_mut/io/simple_window_cleanup_spec.spl
   0/   2    1    0     0     0     0    0  01_unit/lib/nogc_sync_mut/ui/session_shortcut_spec.spl
   0/  14    3    0     0     0     0    0  01_unit/lib/std/type_checker/type_inference_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/compiler/bootstrap_intensive_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_10_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_2_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_3_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_4_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_5_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_6_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_7_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_8_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/type_check_inference_integration_9_spec.spl
   0/   2    2    0     0     0     0    0  02_integration/os/hosted/hosted_external_web_frame_spec.spl
   0/   8    1    0     0     0     0    0  02_integration/sffi/direction_b_import_roundtrip_spec.spl
   0/   3    1    0     0     0     0    0  02_integration/sffi/rsa_sha512_reference_import_spec.spl
   0/   1    1    0     0     0     0    0  03_system/app/browser/feature/browser_focus_editability_order_spec.spl
   0/   1    1    0     0     0     0    0  03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl
   0/ 161    1    0     0     0     0    0  03_system/feature/app/codegen_parity_completion_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/baremetal/allocator_spec.spl
   0/   3    3    0     0     0     0    0  03_system/feature/web_platform/html/html_element_traceability_spec.spl
   0/   0    0    1     0     0     0    0  03_system/gui/capability_negotiation_spec.spl
   0/   0    0    1     0     0     0    0  03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.spl
   0/   0    0    1     0     0     0    0  03_system/os/qemu/os/memory/heap_qemu_spec.spl
   0/   0    0    1     0     0     0    0  03_system/os/qemu/os/memory/memory_cross_qemu_spec.spl
   0/   0    0    1     0     0     0    0  03_system/os/qemu/os/memory/pmm_qemu_spec.spl
   0/   0    0    1     0     0     0    0  03_system/os/qemu/os/memory/vmm_qemu_spec.spl
   0/   0    0    1     0     0     0    0  03_system/os/qemu/os/stress/memory_pressure_qemu_spec.spl
   0/   1    1    0     0     0     0    0  03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.spl
   0/   2    2    0     0     0     0    0  03_system/security/browser_form_action_authorization_spec.spl
   0/   1    1    0     0     0     0    0  03_system/security/browser_hosted_cors_preflight_spec.spl
   0/   1    1    0     0     0     0    0  03_system/security/browser_parent_history_ledger_spec.spl
   0/   1    1    0     0     0     0    0  03_system/security/browser_sandbox_form_navigation_authorization_spec.spl
   0/   2    2    0     0     0     0    0  03_system/security/browser_tls_failure_preservation_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_10_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_11_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_12_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_13_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_14_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_15_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_16_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_17_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_18_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_19_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_1_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_20_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_21_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_22_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_23_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_24_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_25_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_2_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_3_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_4_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_5_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_6_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_7_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_8_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/security/tests/security_9_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/tools/lsp/lib_nogc_sync_lsp_spec.spl
   0/   0    0    1     0     0     0    0  05_perf/llvm_lib_ffi_perf_spec.spl
   0/   0    0    1     0     0     0    0  05_perf/stress/memory_stress_large_spec.spl
   0/   0    0    1     0     0     0    0  05_perf/stress/memory_stress_medium_spec.spl
   0/   0    0    1     0     0     0    0  05_perf/stress/memory_stress_small_spec.spl
   0/   0    0    1     0     0     0    0  perf/llvm_lib_ffi_perf_spec.spl
   0/   0    0    1     0     0     0    0  system/lsp/lib_nogc_sync_lsp_spec.spl
   0/   0    0    1     0     0     0    0  system/qemu/os/ipc/ipc_capability_qemu_spec.spl
   0/   0    0    1     0     0     0    0  system/qemu/os/memory/heap_qemu_spec.spl
   0/   0    0    1     0     0     0    0  system/qemu/os/memory/memory_cross_qemu_spec.spl
   0/   0    0    1     0     0     0    0  system/qemu/os/memory/pmm_qemu_spec.spl
   0/   0    0    1     0     0     0    0  system/qemu/os/memory/vmm_qemu_spec.spl
   0/   0    0    1     0     0     0    0  system/qemu/os/stress/memory_pressure_qemu_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_10_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_11_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_12_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_13_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_14_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_15_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_16_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_17_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_18_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_19_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_1_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_20_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_21_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_22_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_23_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_24_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_25_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_2_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_3_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_4_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_5_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_6_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_7_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_8_system_spec.spl
   0/   0    0    1     0     0     0    0  system/security_tests/security_9_system_spec.spl
```

## MED tier — complete (737 files)

```
vac/tot  weak zero  PASS NOASS INERT TAUT  path
  61/  61    0    0    61     0     0    0  01_unit/app/interpreter/ast_convert_expr_spec.spl
  61/  61    0    0    61     0     0    0  01_unit/compiler/native/simd_check_spec.spl
  55/  55    0    0    55     0     0    0  01_unit/compiler/semantics/const_keys_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_10_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_11_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_12_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_13_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_14_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_15_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_16_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_17_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_18_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_19_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_1_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_20_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_21_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_22_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_23_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_24_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_25_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_2_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_3_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_4_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_5_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_6_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_7_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_8_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler/coverage/branch_coverage_9_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_10_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_11_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_12_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_13_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_14_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_15_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_16_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_17_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_18_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_19_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_1_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_20_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_21_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_22_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_23_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_24_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_25_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_2_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_3_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_4_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_5_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_6_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_7_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_8_spec.spl
  46/  78    0    0     0     0     0   46  01_unit/compiler_core/branch_coverage_9_spec.spl
  42/  42    0    0     0    42     0    0  01_unit/lib/std/parser/error_recovery_spec.spl
  41/  41    0    0    41     0     0    0  01_unit/compiler/macros/macro_check_spec.spl
  41/  41    0    0     0     0     0   41  01_unit/compiler/parser/treesitter_parser_real_spec.spl
  38/  39    0    0     0     0     0   38  01_unit/compiler/parser/treesitter_lexer_real_spec.spl
  38/  38    0    0     0     0     0   38  01_unit/compiler/parser/treesitter_tokenkind_real_spec.spl
  36/  38    0    0     0     0     0   36  03_system/feature/usage/parser_error_recovery_spec.spl
  36/  38    0    0     0     0     0   36  feature/usage/parser_error_recovery_spec.spl
  33/  33    0    0     0     0     0   33  01_unit/compiler/parser/treesitter_tree_real_spec.spl
  30/  30    0    0     0    30     0    0  01_unit/compiler/target_spec_spec.spl
  30/  30    0    0    30     0     0    0  02_integration/compiler/compiler_interpreter_integration_spec.spl
  28/  28    0    0     0     0     0   28  01_unit/compiler/blocks/utils_basic_spec.spl
  26/  26    0    0     0     0     0   26  01_unit/compiler/blocks/builder_api_basic_spec.spl
  26/  31    0    0     0     0     0   26  03_system/feature/usage/parser_deprecation_warnings_spec.spl
  26/  31    0    0     0     0     0   26  feature/usage/parser_deprecation_warnings_spec.spl
  25/  25    0    0     0    25     0    0  01_unit/compiler/.sspec_wrapped_entry_target_spec_spec.spl
  25/  25    0    0     0     0    25    0  01_unit/compiler/backend/rvv_mask_emit_spec.spl [LANDED]
  25/  25    0    0    25     0     0    0  01_unit/compiler/mir/mir_opt_benchmark_spec.spl
  24/  24    0    0    24     0     0    0  01_unit/compiler/type_inference/bidir_check_spec.spl
  23/  44   13    0     0     0    23    0  01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl
  22/  22    0    0     0     0    22    0  01_unit/compiler/backend/rvv_int_emit_spec.spl [LANDED]
  21/  81    0    0     0     0     0   21  01_unit/compiler_core/branch_coverage_27_spec.spl
  20/  20    0    0     0     0    20    0  01_unit/compiler/backend/rvv_float_spec.spl [LANDED]
  20/  20    0    0     0     0    20    0  01_unit/compiler/backend/rvv_widen_spec.spl [LANDED]
  19/  19    0    0     0     0     0   19  01_unit/compiler/blocks/testing_framework_spec.spl
  19/  38    0    0     0     0     0   19  03_system/feature/usage/parser_declarations_spec.spl
  19/  38    0    0     0     0     0   19  feature/usage/parser_declarations_spec.spl
  18/  24    0    0     0    18     0    0  01_unit/compiler/native/inline_asm_matrix_spec.spl
  18/  48    0    0     0     0     0   18  03_system/feature/usage/parser_operators_spec.spl
  18/  48    0    0     0     0     0   18  feature/usage/parser_operators_spec.spl
  17/  17    0    0    17     0     0    0  01_unit/compiler/mono/monomorphize_integration_spec.spl
  16/  56    0    0     0     1     0   15  01_unit/compiler_core/branch_coverage_30_spec.spl
  16/  42    0    0     0     0     0   16  03_system/feature/usage/parser_skip_keyword_spec.spl
  16/  42    0    0     0     0     0   16  feature/usage/parser_skip_keyword_spec.spl
  15/  15    0    0     0     0    15    0  01_unit/app/interpreter/collections/persistent_dict_intensive_spec.spl
  15/  67    0    0     0     0     0   15  01_unit/compiler_core/branch_coverage_28_spec.spl
  15/  33    0    0     0     0     0   15  03_system/feature/usage/parser_type_annotations_spec.spl
  15/  33    0    0     0     0     0   15  feature/usage/parser_type_annotations_spec.spl
  14/  14    0    0     0     0    14    0  01_unit/compiler/backend/encode_rvv_zvk_spec.spl [LANDED]
  14/  14    0    0     0     0    14    0  01_unit/compiler/native/baremetal_syntax_spec.spl
  14/ 128    0    0     0     3    11    0  01_unit/lib/std/compiler/lexer_spec.spl
  14/  33    0    0     0     0     0   14  03_system/feature/features/parser/parser_type_annotations_spec.spl
  14/  33    0    0     0     0     0   14  system/features/parser/parser_type_annotations_spec.spl
  13/  13    0    0     0    13     0    0  01_unit/compiler/import_warning_spec.spl
  12/  12    0    0     0     0     0   12  01_unit/compiler/blocks/easy_api_basic_spec.spl
  12/  12    0    0     0     0     0   12  03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl
  11/  61    0    0     0     0     0   11  01_unit/compiler_core/branch_coverage_29_spec.spl
  11/  21    0    0     0     0     0   11  01_unit/core/complete/hir_types_complete_spec.spl
  11/  21    0    0     0     0     0   11  01_unit/core/complete/lexer_complete_spec.spl
  11/  21    0    0     0     0     0   11  01_unit/core/complete/lexer_struct_complete_spec.spl
  11/  21    0    0     0     0     0   11  01_unit/core/complete/lexer_types_complete_spec.spl
  11/  21    0    0     0     0     0   11  01_unit/core/complete/mir_complete_spec.spl
  11/  21    0    0     0     0     0   11  01_unit/core/complete/mir_types_complete_spec.spl
  11/  21    0    0     0     0     0   11  01_unit/core/complete/parser_complete_spec.spl
  10/  10    0    0     0     0    10    0  01_unit/compiler/backend/rvv_misc_spec.spl [LANDED]
   8/   8    0    0     0     0     0    8  01_unit/compiler/backend/jit_interpreter_spec.spl
   8/  33    0    0     0     0     0    8  03_system/feature/usage/parser_functions_spec.spl
   8/  33    0    0     0     0     0    8  feature/usage/parser_functions_spec.spl
   7/  63    0    0     0     7     0    0  01_unit/compiler/backend/vhdl_backend_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_10_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_11_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_12_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_1_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_2_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_3_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_4_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_5_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_6_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_7_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_8_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler/coverage/auto_coverage_9_spec.spl
   7/  28    0    0     5     2     0    0  01_unit/compiler/loader/jit_context_spec.spl
   7/  14    0    0     0     7     0    0  01_unit/compiler/mir_opt/strength_reduction_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_10_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_11_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_12_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_1_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_2_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_3_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_4_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_5_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_6_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_7_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_8_spec.spl
   7/  20    0    0     0     0     0    7  01_unit/compiler_core/auto_coverage_9_spec.spl
   7/  28    1    0     0     0     0    7  03_system/compiler/ast_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/compiler/code_gen_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/compiler/compiler_driver_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/compiler/diagnostics_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/compiler/lexer_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/compiler/parser_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/compiler/module_import/import_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/feature/features/runtime_system_spec.spl
   7/  28    1    0     0     0     0    7  03_system/interpreter/interpreter_system_spec.spl
   7/  28    1    0     0     0     0    7  system/features/runtime_system_spec.spl
   6/  19    0    0     0     0     0    6  01_unit/compiler/backend/.sspec_wrapped_entry_sspec_system_test_spec.spl
   6/  10    0    0     0     0     0    6  01_unit/compiler/backend/backend_coverage_spec.spl
   6/  19    0    0     0     0     0    6  01_unit/compiler/backend/spipe_system_test_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_alias_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_alias_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_alias_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_dataflow_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_dataflow_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_dataflow_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_escape_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_escape_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_escape_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_liveness_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_liveness_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_liveness_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_purity_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_purity_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/analysis_purity_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_llvm_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_llvm_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_llvm_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_native_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_native_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_native_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_wasm_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_wasm_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/backend_wasm_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_cycle_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_cycle_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_cycle_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_graph_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_graph_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_graph_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_sort_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_sort_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/dependency_sort_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_for_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_for_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_for_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_lambda_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_lambda_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_lambda_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_match_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_match_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/desugar_match_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_builder_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_builder_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_builder_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_validator_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_validator_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/hir_validator_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_expand_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_expand_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_expand_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_hygiene_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_hygiene_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_hygiene_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_resolve_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_resolve_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/macro_resolve_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_builder_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_builder_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_builder_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_transform_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_transform_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_transform_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_validator_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_validator_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/mir_validator_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_cache_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_cache_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_cache_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_loader_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_loader_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_loader_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_resolver_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_resolver_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/module_resolver_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_generic_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_generic_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_generic_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_impl_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_impl_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_impl_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_trait_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_trait_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/monomorphize_trait_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_const_fold_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_const_fold_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_const_fold_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_dce_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_dce_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_dce_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_inline_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_inline_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_inline_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_loop_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_loop_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_loop_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_peephole_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_peephole_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/optimization_peephole_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_fn_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_fn_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_fn_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_module_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_module_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_module_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_type_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_type_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/registry_type_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_binding_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_binding_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_binding_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_lifetime_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_lifetime_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_lifetime_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_scope_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_scope_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/semantics_scope_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_constraint_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_constraint_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_constraint_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_solver_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_solver_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_solver_3_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_unify_1_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_unify_2_spec.spl
   6/  15    0    0     0     0     0    6  01_unit/compiler/deep/type_inference_unify_3_spec.spl
   6/  10    0    0     0     0     0    6  01_unit/compiler_core/ast_coverage_spec.spl
   6/  10    0    0     0     0     0    6  01_unit/compiler_core/mir_coverage_spec.spl
   6/  10    0    0     0     0     0    6  01_unit/compiler_core/types_coverage_spec.spl
   6/  28    1    0     0     0     0    6  03_system/compiler/mir_system_spec.spl
   6/  28    1    0     0     0     0    6  03_system/compiler/optimizer_system_spec.spl
   6/  28    1    0     0     0     0    6  03_system/compiler/symbol_table_system_spec.spl
   6/  28    1    0     0     0     0    6  03_system/compiler/types_system_spec.spl
   6/  15    0    0     0     0     0    6  03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl
   5/   5    0    0     0     5     0    0  01_unit/compiler/parser/cli_spec.spl
   5/   5    0    0     0     5     0    0  01_unit/compiler/parser/optimize_spec.spl
   5/  45    1    0     0     0     0    5  01_unit/compiler_core/branch_coverage_26_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/compiler_driver_complete_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/interpreter_env_complete_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/interpreter_eval_complete_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/interpreter_jit_complete_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/interpreter_mod_complete_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/interpreter_ops_complete_spec.spl
   5/  10    0    0     0     0     0    5  01_unit/core/complete/interpreter_value_complete_spec.spl
   5/   5    0    0     0     0     5    0  03_system/compiler/compiler_sample_spec.spl
   4/   4    0    0     0     0     0    4  01_unit/compiler/bdd_truthy_runtime_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/backend_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/backend_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/backend_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/backend_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/backend_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/dependency_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/dependency_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/dependency_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/dependency_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/dependency_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/desugar_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/desugar_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/desugar_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/desugar_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/desugar_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/driver_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/driver_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/driver_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/driver_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/driver_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/inference_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/inference_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/inference_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/inference_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/inference_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/loader_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/loader_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/loader_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/loader_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/loader_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/mir_opt_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/mir_opt_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/mir_opt_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/mir_opt_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/mir_opt_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/monomorphize_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/monomorphize_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/monomorphize_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/monomorphize_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/monomorphize_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/optimizer_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/optimizer_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/optimizer_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/optimizer_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/optimizer_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/parser_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/parser_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/parser_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/parser_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/parser_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/pipeline_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/pipeline_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/pipeline_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/pipeline_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/pipeline_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/registry_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/registry_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/registry_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/registry_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/registry_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/resolver_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/resolver_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/resolver_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/resolver_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/resolver_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/semantics_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/semantics_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/semantics_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/semantics_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/semantics_5_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_infer_1_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_infer_2_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_infer_3_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_infer_4_complete_spec.spl
   4/  15    0    0     0     0     0    4  01_unit/compiler/complete/type_infer_5_complete_spec.spl
   4/  59    1    0     0     0     0    4  01_unit/compiler/frontend/parser_spec.spl
   4/   6    0    0     0     0     0    4  01_unit/compiler/parser/language_detect_spec.spl
   3/   3    0    0     0     0     0    3  01_unit/compiler/bdd_text_eq_runtime_spec.spl
   3/   9    0    0     0     0     0    3  01_unit/compiler/parser/match_empty_array_bug_spec.spl
   3/   3    0    0     0     3     0    0  02_integration/os/port/native_convergence_spec.spl
   3/  14    0    0     0     3     0    0  03_system/compiler/debug_sidecar_json_order_spec.spl
   3/   9    0    0     0     3     0    0  03_system/compiler/rtl_mdsoc_byte_equal_spec.spl
   3/  33    0    0     0     2     0    1  03_system/feature/features/treesitter/treesitter_parser_spec.spl
   3/  55    0    0     0     1     0    2  03_system/feature/usage/parser_literals_spec.spl
   3/  10    0    0     0     0     0    3  03_system/feature/usage/parser_skip_basic_spec.spl
   3/  20    0    0     0     0     0    3  03_system/interpreter/interpreter_bugs_spec.spl
   3/   6    0    0     0     3     0    0  05_perf/lang/lang_script_vs_compiler_bench_spec.spl
   3/  55    0    0     0     1     0    2  feature/usage/parser_literals_spec.spl
   3/  10    0    0     0     0     0    3  feature/usage/parser_skip_basic_spec.spl
   3/  33    0    0     0     2     0    1  system/features/treesitter/treesitter_parser_spec.spl
   2/   2    0    0     0     2     0    0  01_unit/compiler/r2_lang_probe_spec.spl
   2/  65    0    0     0     2     0    0  01_unit/compiler/backend/stage4_final_symbol_closure_spec.spl
   2/  10    0    0     0     2     0    0  01_unit/compiler/backend/vhdl_clocked_global_state_contract_spec.spl
   2/  35    0    0     0     2     0    0  01_unit/compiler/dependency/macro_import_algorithms_spec.spl
   2/  24    0    0     0     0     0    2  01_unit/compiler/types/type_system_spec.spl
   2/  40    0    0     0     1     0    1  01_unit/compiler_core/compiler_branch_coverage_spec.spl
   2/   3    0    0     0     0     0    2  01_unit/compiler_core/coverage_debug_spec.spl
   2/   2    0    0     0     0     0    2  03_system/compiler/parser_spec.spl
   2/  32    0    0     0     0     0    2  03_system/feature/usage/parser_dual_argument_syntax_spec.spl
   2/  32    0    0     0     0     0    2  feature/usage/parser_dual_argument_syntax_spec.spl
   1/  22    0    0     0     1     0    0  01_unit/app/llm_caret/chat_tui_runtime_spec.spl
   1/   1    0    0     0     0     0    1  01_unit/app/todo/todo_parser_spec.spl
   1/  34    0    0     0     0     1    0  01_unit/app/tooling/test_db_parser_spec.spl
   1/   7    0    0     0     1     0    0  01_unit/app/ui/ui_access_runtime_spec.spl
   1/   6    0    0     0     0     0    1  01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.spl
   1/   7    3    0     0     0     1    0  01_unit/compiler/dict_array_membership_tagged_key_spec.spl
   1/   2    0    0     0     1     0    0  01_unit/compiler/r2_pending_helper_spec.spl
   1/   2    0    0     0     0     0    1  01_unit/compiler/di/export_as_spec.spl
   1/   6    0    0     0     0     1    0  01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl
   1/   1    0    0     0     1     0    0  01_unit/compiler/mir/mir_target_context_spec.spl
   1/  10    0    0     0     0     1    0  01_unit/compiler/native/inline_asm_core_parser_spec.spl
   1/  28    0    0     0     0     1    0  01_unit/compiler/semantics/lint/required_comment_lint_spec.spl
   1/  19    0    0     0     1     0    0  01_unit/compiler_core/branch_coverage_32_spec.spl
   1/  21    0    0     0     0     0    1  01_unit/compiler_core/branch_coverage_35_spec.spl
   1/  18    0    0     0     1     0    0  01_unit/doctest/parser_spec.spl
   1/   3    1    0     0     0     1    0  01_unit/lib/common/js_runtime_host_property_spec.spl
   1/  21    0    0     0     1     0    0  01_unit/lib/common/runtime_parser_bugs_spec.spl
   1/  30    0    0     0     1     0    0  01_unit/std/runtime_parser_bugs_spec.spl
   1/  10    0    0     0     0     0    1  02_integration/e2e/ast_mir_integration_1_spec.spl
   1/  10    0    0     0     0     0    1  02_integration/e2e/lexer_parser_integration_1_spec.spl
   1/  10    0    0     0     0     0    1  02_integration/e2e/mir_backend_integration_1_spec.spl
   1/  10    0    0     0     0     0    1  02_integration/e2e/parser_ast_integration_1_spec.spl
   1/  31    0    0     0     1     0    0  03_system/feature/features/parser/parser_deprecation_warnings_spec.spl
   1/  12    0    0     0     0     0    1  03_system/feature/usage/parser_contextual_keywords_simple_spec.spl
   1/  21    0    0     0     0     0    1  03_system/feature/usage/parser_static_keyword_spec.spl
   1/  36    0    0     0     0     0    1  03_system/feature/usage/parser_syntax_validation_spec.spl
   1/  12    0    0     0     0     0    1  feature/usage/parser_contextual_keywords_simple_spec.spl
   1/  21    0    0     0     0     0    1  feature/usage/parser_static_keyword_spec.spl
   1/  36    0    0     0     0     0    1  feature/usage/parser_syntax_validation_spec.spl
   1/  31    0    0     0     1     0    0  system/features/parser/parser_deprecation_warnings_spec.spl
   0/   3    1    0     0     0     0    0  01_unit/app/ui/host_wm_runtime_loop_spec.spl
   0/  11    1    0     0     0     0    0  01_unit/compiler/backend/interpreter_backend_spec.spl
   0/   0    0    1     0     0     0    0  01_unit/compiler/hir/hir_eval_spec.spl
   0/   0    0    1     0     0     0    0  01_unit/compiler/hir/hir_lower_spec.spl
   0/   0    0    1     0     0     0    0  01_unit/compiler/hir/hir_module_spec.spl
   0/   0    0    1     0     0     0    0  01_unit/compiler/hir/hir_types_spec.spl
   0/   3    1    0     0     0     0    0  01_unit/compiler/loader/runtime_surface_spec.spl
   0/  11    1    0     0     0     0    0  01_unit/compiler/loader/settlement_exports_contract_spec.spl
   0/   1    1    0     0     0     0    0  01_unit/compiler/mir_opt/optimization_pipeline_aggregate_transport_source_spec.spl
   0/  12    3    0     0     0     0    0  01_unit/compiler/native/asm_match_spec.spl
   0/  10   10    0     0     0     0    0  01_unit/lib/common/compress/zstd_sequence_parser_bounds_spec.spl
   0/   1    1    0     0     0     0    0  01_unit/lib/common/web/browser_session_dom_generation_runtime_spec.spl
   0/   2    2    0     0     0     0    0  01_unit/lib/gpu/engine2d/font_runtime_config_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/app/io_runtime_import_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/compiler/c_backend_e2e_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/compiler/compiler_intensive_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/compiler/llvm_native_link_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/compiler/native_backend_e2e_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_10_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_2_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_3_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_4_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_5_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_6_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_7_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_8_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/ast_mir_integration_9_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_10_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_2_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_3_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_4_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_5_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_6_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_7_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_8_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/lexer_parser_integration_9_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_10_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_2_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_3_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_4_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_5_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_6_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_7_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_8_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/mir_backend_integration_9_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_10_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_2_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_3_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_4_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_5_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_6_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_7_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_8_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/e2e/parser_ast_integration_9_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/io/native_ops_dir_create_all_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/io/native_ops_dir_create_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/io/native_ops_dir_recursive_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/io/native_ops_file_copy_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/io/native_ops_file_read_write_spec.spl
   0/   8    1    0     0     0     0    0  02_integration/os/port/llvm/smoke_clang_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/baremetal_library_host_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/ch32v307_composite_runner_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/qemu_arm_composite_runner_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/qemu_rv32_composite_runner_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/qemu_rv32_library_semihost_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/qemu_rv64_semihost_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/stm32h7_composite_runner_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/stm32h7_e2e_jit_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/stm32h7_minimal_spec.spl
   0/   0    0    1     0     0     0    0  02_integration/remote_jit/stm32wb_composite_runner_spec.spl
   0/   0    0    1     0     0     0    0  03_system/check/llvm_simd_row_native_arch_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/native_backend_e2e_system_spec.spl
   0/   2    1    0     0     0     0    0  03_system/compiler/native_cli_mode_transport_regression_spec.spl
   0/   1    1    0     0     0     0    0  03_system/compiler/native_platform_path_owner_regression_spec.spl
   0/   1    1    0     0     0     0    0  03_system/compiler/native_struct_field_access_regression_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/vhdl_backend_system_spec.spl
   0/  46    1    0     0     0     0    0  03_system/compiler/vhdl_clocked_testbench_conversion_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/vhdl_mir_backend_call_port_map_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/vhdl_mir_backend_multi_output_spec.spl
   0/  39    2    0     0     0     0    0  03_system/compiler/vhdl_testbench_conversion_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_10_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_11_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_12_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_13_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_14_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_15_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_16_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_17_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_18_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_19_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_1_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_20_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_21_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_22_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_23_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_24_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_25_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_26_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_27_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_28_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_29_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_2_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_30_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_31_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_32_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_33_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_34_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_35_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_36_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_37_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_38_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_39_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_3_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_40_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_41_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_42_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_43_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_44_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_45_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_46_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_47_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_48_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_49_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_4_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_50_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_5_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_6_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_7_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_8_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/comprehensive/compiler_comprehensive_9_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_10_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_11_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_12_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_13_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_14_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_15_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_16_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_17_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_18_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_19_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_1_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_20_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_21_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_22_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_23_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_24_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_25_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_26_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_27_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_28_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_29_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_2_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_30_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_31_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_32_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_33_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_34_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_35_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_36_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_37_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_38_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_39_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_3_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_40_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_41_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_42_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_43_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_44_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_45_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_46_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_47_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_48_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_49_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_4_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_50_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_5_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_6_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_7_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_8_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/compiler/runtime_comprehensive/runtime_comprehensive_9_system_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/compiler_services_error_cases_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/compiler_services_feature_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/ch32v307_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/ghdl_rv32_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/qemu_arm_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/qemu_rv32_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/stm32h7_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/stm32wb_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/feature/app/remote_jit/trace32_stm32wb_jit_e2e_spec.spl
   0/   0    0    1     0     0     0    0  03_system/gui/native_gui_build_spec.spl
   0/   0    0    1     0     0     0    0  03_system/gui/windows_native_mdi_evidence_spec.spl
   0/   0    0    1     0     0     0    0  03_system/tools/lint/compiler_lint_spec.spl
   0/   0    0    1     0     0     0    0  03_system/tools/lsp/compiler_00_15_lsp_spec.spl
   0/   0    0    1     0     0     0    0  03_system/tools/lsp/compiler_20_35_lsp_spec.spl
   0/   0    0    1     0     0     0    0  03_system/tools/lsp/compiler_40_60_lsp_spec.spl
   0/   0    0    1     0     0     0    0  03_system/tools/lsp/compiler_70_lsp_spec.spl
   0/   0    0    1     0     0     0    0  03_system/tools/lsp/compiler_80_99_lsp_spec.spl
   0/   0    0    1     0     0     0    0  05_perf/compiler_perf_baseline_spec.spl
   0/   0    0    1     0     0     0    0  05_perf/native_layout_performance_spec.spl
   0/   9    1    0     0     0     0    0  feature/usage/math_autograd_runtime_spec.spl
   0/   0    0    1     0     0     0    0  perf/compiler_perf_baseline_spec.spl
   0/   0    0    1     0     0     0    0  perf/native_layout_performance_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_10_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_11_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_12_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_13_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_14_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_15_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_16_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_17_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_18_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_19_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_1_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_20_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_21_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_22_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_23_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_24_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_25_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_26_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_27_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_28_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_29_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_2_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_30_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_31_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_32_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_33_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_34_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_35_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_36_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_37_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_38_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_39_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_3_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_40_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_41_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_42_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_43_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_44_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_45_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_46_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_47_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_48_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_49_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_4_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_50_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_5_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_6_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_7_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_8_system_spec.spl
   0/   0    0    1     0     0     0    0  system/compiler_comprehensive/compiler_comprehensive_9_system_spec.spl
   0/   0    0    1     0     0     0    0  system/lint/compiler_lint_spec.spl
   0/   0    0    1     0     0     0    0  system/lsp/compiler_00_15_lsp_spec.spl
   0/   0    0    1     0     0     0    0  system/lsp/compiler_20_35_lsp_spec.spl
   0/   0    0    1     0     0     0    0  system/lsp/compiler_40_60_lsp_spec.spl
   0/   0    0    1     0     0     0    0  system/lsp/compiler_70_lsp_spec.spl
   0/   0    0    1     0     0     0    0  system/lsp/compiler_80_99_lsp_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_10_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_11_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_12_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_13_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_14_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_15_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_16_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_17_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_18_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_19_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_1_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_20_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_21_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_22_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_23_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_24_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_25_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_26_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_27_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_28_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_29_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_2_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_30_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_31_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_32_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_33_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_34_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_35_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_36_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_37_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_38_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_39_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_3_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_40_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_41_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_42_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_43_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_44_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_45_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_46_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_47_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_48_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_49_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_4_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_50_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_5_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_6_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_7_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_8_system_spec.spl
   0/   0    0    1     0     0     0    0  system/runtime_comprehensive/runtime_comprehensive_9_system_spec.spl
```

## LOW tier — 4064 files, rolled up by family

Dominated by auto-generated literal-only families (section 4). These
should be deleted or rewritten wholesale, not patched file by file.

```
files  vac_examples  family (digits collapsed to N)
   25          1150  01_unit/app/branch_coverageNspec.spl
   25          1150  01_unit/lib/branch_coverageNspec.spl
   20           400  01_unit/std/deep/array_deepNspec.spl
   20           400  01_unit/std/deep/async_deepNspec.spl
   20           400  01_unit/std/deep/dict_deepNspec.spl
   20           400  01_unit/std/deep/error_deepNspec.spl
   20           400  01_unit/std/deep/io_deepNspec.spl
   20           400  01_unit/std/deep/json_deepNspec.spl
   20           400  01_unit/std/deep/option_deepNspec.spl
   20           400  01_unit/std/deep/path_deepNspec.spl
   20           400  01_unit/std/deep/spec_deepNspec.spl
   20           400  01_unit/std/deep/string_deepNspec.spl
   30           180  01_unit/lib/common/auto_comprehensiveNspec.spl
   30           180  01_unit/std/auto_comprehensiveNspec.spl
   12            84  01_unit/app/auto_coverageNspec.spl
   12            84  01_unit/lib/auto_coverageNspec.spl
    1            63  01_unit/spec/matchers_spec.spl
    1            61  01_unit/app/test_runner/quickcheck_spec.spl
   50            50  02_integration/core/core_integrationNspec.spl
    1            43  03_system/feature/usage/arithmetic_spec.spl
    1            43  feature/usage/arithmetic_spec.spl
    1            41  03_system/feature/web_platform/css/selector_color_subset_spec.spl
    1            36  01_unit/app/ui/gui_widgets_spec.spl
    1            32  01_unit/app/test_runner/integration_spec.spl
    1            32  03_system/feature/usage/static_const_declarations_spec.spl
    1            32  feature/usage/static_const_declarations_spec.spl
    1            31  01_unit/app/ui/vulkan_window_spec.spl
    1            31  01_unit/lib/std/testing/mock_spec.spl
    1            31  02_integration/spec/coverage_spec.spl
    1            31  system/coupling_analysis_spec.spl
    5            30  01_unit/std/complete/argsNcomplete_spec.spl
    5            30  01_unit/std/complete/arrayNcomplete_spec.spl
    5            30  01_unit/std/complete/assertNcomplete_spec.spl
    5            30  01_unit/std/complete/asyncNcomplete_spec.spl
    5            30  01_unit/std/complete/atomicNcomplete_spec.spl
    5            30  01_unit/std/complete/channelNcomplete_spec.spl
    5            30  01_unit/std/complete/collectionsNcomplete_spec.spl
    5            30  01_unit/std/complete/concurrentNcomplete_spec.spl
    5            30  01_unit/std/complete/configNcomplete_spec.spl
    5            30  01_unit/std/complete/debugNcomplete_spec.spl
    5            30  01_unit/std/complete/dictNcomplete_spec.spl
    5            30  01_unit/std/complete/envNcomplete_spec.spl
    5            30  01_unit/std/complete/errorNcomplete_spec.spl
    5            30  01_unit/std/complete/flagsNcomplete_spec.spl
    5            30  01_unit/std/complete/formatNcomplete_spec.spl
    5            30  01_unit/std/complete/fsNcomplete_spec.spl
    5            30  01_unit/std/complete/hashNcomplete_spec.spl
    5            30  01_unit/std/complete/ioNcomplete_spec.spl
    5            30  01_unit/std/complete/iterNcomplete_spec.spl
    5            30  01_unit/std/complete/jsonNcomplete_spec.spl
    5            30  01_unit/std/complete/listNcomplete_spec.spl
    5            30  01_unit/std/complete/logNcomplete_spec.spl
    5            30  01_unit/std/complete/mathNcomplete_spec.spl
    5            30  01_unit/std/complete/mutexNcomplete_spec.spl
    5            30  01_unit/std/complete/netNcomplete_spec.spl
    5            30  01_unit/std/complete/optionNcomplete_spec.spl
    5            30  01_unit/std/complete/parseNcomplete_spec.spl
    5            30  01_unit/std/complete/pathNcomplete_spec.spl
    5            30  01_unit/std/complete/processNcomplete_spec.spl
    5            30  01_unit/std/complete/randomNcomplete_spec.spl
    5            30  01_unit/std/complete/rangeNcomplete_spec.spl
    5            30  01_unit/std/complete/regexNcomplete_spec.spl
    5            30  01_unit/std/complete/resultNcomplete_spec.spl
    5            30  01_unit/std/complete/sdnNcomplete_spec.spl
    5            30  01_unit/std/complete/setNcomplete_spec.spl
    5            30  01_unit/std/complete/specNcomplete_spec.spl
    5            30  01_unit/std/complete/stringNcomplete_spec.spl
    5            30  01_unit/std/complete/testNcomplete_spec.spl
    5            30  01_unit/std/complete/timeNcomplete_spec.spl
    5            30  01_unit/std/complete/tupleNcomplete_spec.spl
    1            29  03_system/feature/features/baremetal/volatile_spec.spl
    1            29  system/features/baremetal/volatile_spec.spl
    1            28  03_system/feature/usage/async_features_spec.spl
    1            28  feature/usage/async_features_spec.spl
    1            27  feature/usage/aop_architecture_rules_spec.spl
    1            26  01_unit/app/ui/widgets_spec.spl
    1            26  01_unit/lib/std/spec/decorators_spec.spl
    1            24  03_system/feature/language/concurrency_spec.spl
    1            22  01_unit/app/ui/theme_spec.spl
    1            22  01_unit/lib/common/smoke_test_spec.spl
    1            22  01_unit/std/smoke_test_spec.spl
    1            21  03_system/feature/usage/alias_deprecated_spec.spl
    1            21  feature/usage/alias_deprecated_spec.spl
    1            20  01_unit/app/ui/element_spec.spl
    1            19  03_system/feature/features/baremetal/const_fn_spec.spl
    1            19  03_system/generated/context_performance_spec.spl
    1            19  system/features/baremetal/const_fn_spec.spl
    1            18  01_unit/app/ui/diff_spec.spl
    1            18  01_unit/app/ui/html_spec.spl
    1            17  01_unit/app/tooling/test_args_spec.spl
    1            16  01_unit/app/mcp_unit/fileio_protection_spec.spl
    1            15  03_system/feature/usage/syntax_spec.spl
    1            15  03_system/gui/editor_gui_sdl_spec.spl
    1            15  feature/usage/syntax_spec.spl
    1            15  system/editor_gui_sdl_spec.spl
    1            14  01_unit/app/ui/patchset_spec.spl
    1            14  01_unit/spec/progress_spec.spl
    1            14  03_system/feature/usage/generics_spec.spl
    1            14  feature/usage/generics_spec.spl
    1            13  03_system/feature/usage/set_literal_spec.spl
    1            13  03_system/generated/spec_framework_spec.spl
    1            13  feature/usage/set_literal_spec.spl
    1            12  01_unit/lib/viz/aggregator_compose_spec.spl
    1            12  01_unit/spec/expect_spec.spl
    1            12  03_system/feature/usage/effect_annotations_spec.spl
    1            12  feature/usage/effect_annotations_spec.spl
    1            12  shared/core/comparison_spec.spl
    1            12  shared/types/union_impl_spec.spl
    1            11  01_unit/app/tooling/test_db_concurrency_spec.spl
    1            11  01_unit/core/complete/aop_complete_spec.spl
    1            11  01_unit/core/complete/ast_complete_spec.spl
    1            11  01_unit/core/complete/ast_types_complete_spec.spl
    1            11  01_unit/core/complete/backend_types_complete_spec.spl
    1            11  01_unit/core/complete/error_complete_spec.spl
    1            11  01_unit/core/complete/tokens_complete_spec.spl
    1            11  01_unit/core/complete/types_complete_spec.spl
    1            11  01_unit/os/kernel/arch/syscall_dispatch_spec.spl
    1            11  01_unit/std/improved/args_edge_spec.spl
    1            11  01_unit/std/improved/args_error_spec.spl
    1            11  01_unit/std/improved/args_integration_spec.spl
    1            11  01_unit/std/improved/args_unit_spec.spl
    1            11  01_unit/std/improved/array_edge_spec.spl
    1            11  01_unit/std/improved/array_error_spec.spl
    1            11  01_unit/std/improved/array_integration_spec.spl
    1            11  01_unit/std/improved/array_unit_spec.spl
    1            11  01_unit/std/improved/assert_edge_spec.spl
    1            11  01_unit/std/improved/assert_error_spec.spl
    1            11  01_unit/std/improved/assert_integration_spec.spl
    1            11  01_unit/std/improved/assert_unit_spec.spl
    1            11  01_unit/std/improved/async_edge_spec.spl
    1            11  01_unit/std/improved/async_error_spec.spl
    1            11  01_unit/std/improved/async_integration_spec.spl
    1            11  01_unit/std/improved/async_unit_spec.spl
    1            11  01_unit/std/improved/atomic_edge_spec.spl
    1            11  01_unit/std/improved/atomic_error_spec.spl
    1            11  01_unit/std/improved/atomic_integration_spec.spl
    1            11  01_unit/std/improved/atomic_unit_spec.spl
    1            11  01_unit/std/improved/await_edge_spec.spl
    1            11  01_unit/std/improved/await_error_spec.spl
    1            11  01_unit/std/improved/await_integration_spec.spl
    1            11  01_unit/std/improved/await_unit_spec.spl
    1            11  01_unit/std/improved/backtrace_edge_spec.spl
    1            11  01_unit/std/improved/backtrace_error_spec.spl
    1            11  01_unit/std/improved/backtrace_integration_spec.spl
    1            11  01_unit/std/improved/backtrace_unit_spec.spl
    1            11  01_unit/std/improved/benchmark_edge_spec.spl
    1            11  01_unit/std/improved/benchmark_error_spec.spl
    1            11  01_unit/std/improved/benchmark_integration_spec.spl
    1            11  01_unit/std/improved/benchmark_unit_spec.spl
    1            11  01_unit/std/improved/bool_edge_spec.spl
    1            11  01_unit/std/improved/bool_error_spec.spl
    1            11  01_unit/std/improved/bool_integration_spec.spl
    1            11  01_unit/std/improved/bool_unit_spec.spl
    1            11  01_unit/std/improved/buffer_edge_spec.spl
    1            11  01_unit/std/improved/buffer_error_spec.spl
    1            11  01_unit/std/improved/buffer_integration_spec.spl
    1            11  01_unit/std/improved/buffer_unit_spec.spl
    1            11  01_unit/std/improved/channel_edge_spec.spl
    1            11  01_unit/std/improved/channel_error_spec.spl
    1            11  01_unit/std/improved/channel_integration_spec.spl
    1            11  01_unit/std/improved/channel_unit_spec.spl
    1            11  01_unit/std/improved/char_edge_spec.spl
    1            11  01_unit/std/improved/char_error_spec.spl
    1            11  01_unit/std/improved/char_integration_spec.spl
    1            11  01_unit/std/improved/char_unit_spec.spl
    1            11  01_unit/std/improved/check_edge_spec.spl
    1            11  01_unit/std/improved/check_error_spec.spl
    1            11  01_unit/std/improved/check_integration_spec.spl
    1            11  01_unit/std/improved/check_unit_spec.spl
    1            11  01_unit/std/improved/compress_edge_spec.spl
    1            11  01_unit/std/improved/compress_error_spec.spl
    1            11  01_unit/std/improved/compress_integration_spec.spl
    1            11  01_unit/std/improved/compress_unit_spec.spl
    1            11  01_unit/std/improved/config_edge_spec.spl
    1            11  01_unit/std/improved/config_error_spec.spl
    1            11  01_unit/std/improved/config_integration_spec.spl
    1            11  01_unit/std/improved/config_unit_spec.spl
    1            11  01_unit/std/improved/convert_edge_spec.spl
    1            11  01_unit/std/improved/convert_error_spec.spl
    1            11  01_unit/std/improved/convert_integration_spec.spl
    1            11  01_unit/std/improved/convert_unit_spec.spl
    1            11  01_unit/std/improved/date_edge_spec.spl
    1            11  01_unit/std/improved/date_error_spec.spl
    1            11  01_unit/std/improved/date_integration_spec.spl
    1            11  01_unit/std/improved/date_unit_spec.spl
    1            11  01_unit/std/improved/debug_edge_spec.spl
    1            11  01_unit/std/improved/debug_error_spec.spl
    1            11  01_unit/std/improved/debug_integration_spec.spl
    1            11  01_unit/std/improved/debug_unit_spec.spl
    1            11  01_unit/std/improved/decode_edge_spec.spl
    1            11  01_unit/std/improved/decode_error_spec.spl
    1            11  01_unit/std/improved/decode_integration_spec.spl
    1            11  01_unit/std/improved/decode_unit_spec.spl
    1            11  01_unit/std/improved/dict_edge_spec.spl
    1            11  01_unit/std/improved/dict_error_spec.spl
    1            11  01_unit/std/improved/dict_integration_spec.spl
    1            11  01_unit/std/improved/dict_unit_spec.spl
    1            11  01_unit/std/improved/dir_edge_spec.spl
    1            11  01_unit/std/improved/dir_error_spec.spl
    1            11  01_unit/std/improved/dir_integration_spec.spl
    1            11  01_unit/std/improved/dir_unit_spec.spl
    1            11  01_unit/std/improved/duration_edge_spec.spl
    1            11  01_unit/std/improved/duration_error_spec.spl
    1            11  01_unit/std/improved/duration_integration_spec.spl
    1            11  01_unit/std/improved/duration_unit_spec.spl
    1            11  01_unit/std/improved/encode_edge_spec.spl
    1            11  01_unit/std/improved/encode_error_spec.spl
    1            11  01_unit/std/improved/encode_integration_spec.spl
    1            11  01_unit/std/improved/encode_unit_spec.spl
    1            11  01_unit/std/improved/env_edge_spec.spl
    1            11  01_unit/std/improved/env_error_spec.spl
    1            11  01_unit/std/improved/env_integration_spec.spl
    1            11  01_unit/std/improved/env_unit_spec.spl
    1            11  01_unit/std/improved/error_edge_spec.spl
    1            11  01_unit/std/improved/error_error_spec.spl
    1            11  01_unit/std/improved/error_integration_spec.spl
    1            11  01_unit/std/improved/error_unit_spec.spl
    1            11  01_unit/std/improved/exit_edge_spec.spl
    1            11  01_unit/std/improved/exit_error_spec.spl
    1            11  01_unit/std/improved/exit_integration_spec.spl
    1            11  01_unit/std/improved/exit_unit_spec.spl
    1            11  01_unit/std/improved/expect_edge_spec.spl
    1            11  01_unit/std/improved/expect_error_spec.spl
    1            11  01_unit/std/improved/expect_integration_spec.spl
    1            11  01_unit/std/improved/expect_unit_spec.spl
    1            11  01_unit/std/improved/file_edge_spec.spl
    1            11  01_unit/std/improved/file_error_spec.spl
    1            11  01_unit/std/improved/file_integration_spec.spl
    1            11  01_unit/std/improved/file_unit_spec.spl
    1            11  01_unit/std/improved/filter_edge_spec.spl
    1            11  01_unit/std/improved/filter_error_spec.spl
    1            11  01_unit/std/improved/filter_integration_spec.spl
    1            11  01_unit/std/improved/filter_unit_spec.spl
    1            11  01_unit/std/improved/fixture_edge_spec.spl
    1            11  01_unit/std/improved/fixture_error_spec.spl
    1            11  01_unit/std/improved/fixture_integration_spec.spl
    1            11  01_unit/std/improved/fixture_unit_spec.spl
    1            11  01_unit/std/improved/flags_edge_spec.spl
    1            11  01_unit/std/improved/flags_error_spec.spl
    1            11  01_unit/std/improved/flags_integration_spec.spl
    1            11  01_unit/std/improved/flags_unit_spec.spl
    1            11  01_unit/std/improved/float_edge_spec.spl
    1            11  01_unit/std/improved/float_error_spec.spl
    1            11  01_unit/std/improved/float_integration_spec.spl
    1            11  01_unit/std/improved/float_unit_spec.spl
    1            11  01_unit/std/improved/format_edge_spec.spl
    1            11  01_unit/std/improved/format_error_spec.spl
    1            11  01_unit/std/improved/format_integration_spec.spl
    1            11  01_unit/std/improved/format_unit_spec.spl
    1            11  01_unit/std/improved/fs_edge_spec.spl
    1            11  01_unit/std/improved/fs_error_spec.spl
    1            11  01_unit/std/improved/fs_integration_spec.spl
    1            11  01_unit/std/improved/fs_unit_spec.spl
    1            11  01_unit/std/improved/future_edge_spec.spl
    1            11  01_unit/std/improved/future_error_spec.spl
    1            11  01_unit/std/improved/future_integration_spec.spl
    1            11  01_unit/std/improved/future_unit_spec.spl
    1            11  01_unit/std/improved/glob_edge_spec.spl
    1            11  01_unit/std/improved/glob_error_spec.spl
    1            11  01_unit/std/improved/glob_integration_spec.spl
    1            11  01_unit/std/improved/glob_unit_spec.spl
    1            11  01_unit/std/improved/hash_edge_spec.spl
    1            11  01_unit/std/improved/hash_error_spec.spl
    1            11  01_unit/std/improved/hash_func_edge_spec.spl
    1            11  01_unit/std/improved/hash_func_error_spec.spl
    1            11  01_unit/std/improved/hash_func_integration_spec.spl
    1            11  01_unit/std/improved/hash_func_unit_spec.spl
    1            11  01_unit/std/improved/hash_integration_spec.spl
    1            11  01_unit/std/improved/hash_unit_spec.spl
    1            11  01_unit/std/improved/http_edge_spec.spl
    1            11  01_unit/std/improved/http_error_spec.spl
    1            11  01_unit/std/improved/http_integration_spec.spl
    1            11  01_unit/std/improved/http_unit_spec.spl
    1            11  01_unit/std/improved/instant_edge_spec.spl
    1            11  01_unit/std/improved/instant_error_spec.spl
    1            11  01_unit/std/improved/instant_integration_spec.spl
    1            11  01_unit/std/improved/instant_unit_spec.spl
    1            11  01_unit/std/improved/int_edge_spec.spl
    1            11  01_unit/std/improved/int_error_spec.spl
    1            11  01_unit/std/improved/int_integration_spec.spl
    1            11  01_unit/std/improved/int_unit_spec.spl
    1            11  01_unit/std/improved/io_edge_spec.spl
    1            11  01_unit/std/improved/io_error_spec.spl
    1            11  01_unit/std/improved/io_integration_spec.spl
    1            11  01_unit/std/improved/io_unit_spec.spl
    1            11  01_unit/std/improved/iter_edge_spec.spl
    1            11  01_unit/std/improved/iter_error_spec.spl
    1            11  01_unit/std/improved/iter_integration_spec.spl
    1            11  01_unit/std/improved/iter_unit_spec.spl
    1            11  01_unit/std/improved/join_edge_spec.spl
    1            11  01_unit/std/improved/join_error_spec.spl
    1            11  01_unit/std/improved/join_integration_spec.spl
    1            11  01_unit/std/improved/join_unit_spec.spl
    1            11  01_unit/std/improved/json_edge_spec.spl
    1            11  01_unit/std/improved/json_error_spec.spl
    1            11  01_unit/std/improved/json_integration_spec.spl
    1            11  01_unit/std/improved/json_unit_spec.spl
    1            11  01_unit/std/improved/list_edge_spec.spl
    1            11  01_unit/std/improved/list_error_spec.spl
    1            11  01_unit/std/improved/list_integration_spec.spl
    1            11  01_unit/std/improved/list_unit_spec.spl
    1            11  01_unit/std/improved/log_edge_spec.spl
    1            11  01_unit/std/improved/log_error_spec.spl
    1            11  01_unit/std/improved/log_integration_spec.spl
    1            11  01_unit/std/improved/log_unit_spec.spl
    1            11  01_unit/std/improved/macro_edge_spec.spl
    1            11  01_unit/std/improved/macro_error_spec.spl
    1            11  01_unit/std/improved/macro_integration_spec.spl
    1            11  01_unit/std/improved/macro_unit_spec.spl
    1            11  01_unit/std/improved/map_edge_spec.spl
    1            11  01_unit/std/improved/map_error_spec.spl
    1            11  01_unit/std/improved/map_integration_spec.spl
    1            11  01_unit/std/improved/map_unit_spec.spl
    1            11  01_unit/std/improved/match_edge_spec.spl
    1            11  01_unit/std/improved/match_error_spec.spl
    1            11  01_unit/std/improved/match_integration_spec.spl
    1            11  01_unit/std/improved/match_unit_spec.spl
    1            11  01_unit/std/improved/math_edge_spec.spl
    1            11  01_unit/std/improved/math_error_spec.spl
    1            11  01_unit/std/improved/math_integration_spec.spl
    1            11  01_unit/std/improved/math_unit_spec.spl
    1            11  01_unit/std/improved/meta_edge_spec.spl
    1            11  01_unit/std/improved/meta_error_spec.spl
    1            11  01_unit/std/improved/meta_integration_spec.spl
    1            11  01_unit/std/improved/meta_unit_spec.spl
    1            11  01_unit/std/improved/mock_edge_spec.spl
    1            11  01_unit/std/improved/mock_error_spec.spl
    1            11  01_unit/std/improved/mock_integration_spec.spl
    1            11  01_unit/std/improved/mock_unit_spec.spl
    1            11  01_unit/std/improved/mutex_edge_spec.spl
    1            11  01_unit/std/improved/mutex_error_spec.spl
    1            11  01_unit/std/improved/mutex_integration_spec.spl
    1            11  01_unit/std/improved/mutex_unit_spec.spl
    1            11  01_unit/std/improved/net_edge_spec.spl
    1            11  01_unit/std/improved/net_error_spec.spl
    1            11  01_unit/std/improved/net_integration_spec.spl
    1            11  01_unit/std/improved/net_unit_spec.spl
    1            11  01_unit/std/improved/option_edge_spec.spl
    1            11  01_unit/std/improved/option_error_spec.spl
    1            11  01_unit/std/improved/option_integration_spec.spl
    1            11  01_unit/std/improved/option_unit_spec.spl
    1            11  01_unit/std/improved/panic_edge_spec.spl
    1            11  01_unit/std/improved/panic_error_spec.spl
    1            11  01_unit/std/improved/panic_integration_spec.spl
    1            11  01_unit/std/improved/panic_unit_spec.spl
    1            11  01_unit/std/improved/parse_edge_spec.spl
    1            11  01_unit/std/improved/parse_error_spec.spl
    1            11  01_unit/std/improved/parse_integration_spec.spl
    1            11  01_unit/std/improved/parse_unit_spec.spl
    1            11  01_unit/std/improved/path_edge_spec.spl
    1            11  01_unit/std/improved/path_error_spec.spl
    1            11  01_unit/std/improved/path_integration_spec.spl
    1            11  01_unit/std/improved/path_unit_spec.spl
    1            11  01_unit/std/improved/pattern_edge_spec.spl
    1            11  01_unit/std/improved/pattern_error_spec.spl
    1            11  01_unit/std/improved/pattern_integration_spec.spl
    1            11  01_unit/std/improved/pattern_unit_spec.spl
    1            11  01_unit/std/improved/pool_edge_spec.spl
    1            11  01_unit/std/improved/pool_error_spec.spl
    1            11  01_unit/std/improved/pool_integration_spec.spl
    1            11  01_unit/std/improved/pool_unit_spec.spl
    1            11  01_unit/std/improved/process_edge_spec.spl
    1            11  01_unit/std/improved/process_error_spec.spl
    1            11  01_unit/std/improved/process_integration_spec.spl
    1            11  01_unit/std/improved/process_unit_spec.spl
    1            11  01_unit/std/improved/profile_edge_spec.spl
    1            11  01_unit/std/improved/profile_error_spec.spl
    1            11  01_unit/std/improved/profile_integration_spec.spl
    1            11  01_unit/std/improved/profile_unit_spec.spl
    1            11  01_unit/std/improved/promise_edge_spec.spl
    1            11  01_unit/std/improved/promise_error_spec.spl
    1            11  01_unit/std/improved/promise_integration_spec.spl
    1            11  01_unit/std/improved/promise_unit_spec.spl
    1            11  01_unit/std/improved/queue_edge_spec.spl
    1            11  01_unit/std/improved/queue_error_spec.spl
    1            11  01_unit/std/improved/queue_integration_spec.spl
    1            11  01_unit/std/improved/queue_unit_spec.spl
    1            11  01_unit/std/improved/random_edge_spec.spl
    1            11  01_unit/std/improved/random_error_spec.spl
    1            11  01_unit/std/improved/random_integration_spec.spl
    1            11  01_unit/std/improved/random_unit_spec.spl
    1            11  01_unit/std/improved/range_edge_spec.spl
    1            11  01_unit/std/improved/range_error_spec.spl
    1            11  01_unit/std/improved/range_integration_spec.spl
    1            11  01_unit/std/improved/range_unit_spec.spl
    1            11  01_unit/std/improved/reader_edge_spec.spl
    1            11  01_unit/std/improved/reader_error_spec.spl
    1            11  01_unit/std/improved/reader_integration_spec.spl
    1            11  01_unit/std/improved/reader_unit_spec.spl
    1            11  01_unit/std/improved/recover_edge_spec.spl
    1            11  01_unit/std/improved/recover_error_spec.spl
    1            11  01_unit/std/improved/recover_integration_spec.spl
    1            11  01_unit/std/improved/recover_unit_spec.spl
    1            11  01_unit/std/improved/reduce_edge_spec.spl
    1            11  01_unit/std/improved/reduce_error_spec.spl
    1            11  01_unit/std/improved/reduce_integration_spec.spl
    1            11  01_unit/std/improved/reduce_unit_spec.spl
    1            11  01_unit/std/improved/reflect_edge_spec.spl
    1            11  01_unit/std/improved/reflect_error_spec.spl
    1            11  01_unit/std/improved/reflect_integration_spec.spl
    1            11  01_unit/std/improved/reflect_unit_spec.spl
    1            11  01_unit/std/improved/regex_edge_spec.spl
    1            11  01_unit/std/improved/regex_error_spec.spl
    1            11  01_unit/std/improved/regex_integration_spec.spl
    1            11  01_unit/std/improved/regex_unit_spec.spl
    1            11  01_unit/std/improved/result_edge_spec.spl
    1            11  01_unit/std/improved/result_error_spec.spl
    1            11  01_unit/std/improved/result_integration_spec.spl
    1            11  01_unit/std/improved/result_unit_spec.spl
    1            11  01_unit/std/improved/rwlock_edge_spec.spl
    1            11  01_unit/std/improved/rwlock_error_spec.spl
    1            11  01_unit/std/improved/rwlock_integration_spec.spl
    1            11  01_unit/std/improved/rwlock_unit_spec.spl
    1            11  01_unit/std/improved/sdn_edge_spec.spl
    1            11  01_unit/std/improved/sdn_error_spec.spl
    1            11  01_unit/std/improved/sdn_integration_spec.spl
    1            11  01_unit/std/improved/sdn_unit_spec.spl
    1            11  01_unit/std/improved/search_edge_spec.spl
    1            11  01_unit/std/improved/search_error_spec.spl
    1            11  01_unit/std/improved/search_integration_spec.spl
    1            11  01_unit/std/improved/search_unit_spec.spl
    1            11  01_unit/std/improved/semaphore_edge_spec.spl
    1            11  01_unit/std/improved/semaphore_error_spec.spl
    1            11  01_unit/std/improved/semaphore_integration_spec.spl
    1            11  01_unit/std/improved/semaphore_unit_spec.spl
    1            11  01_unit/std/improved/serialize_edge_spec.spl
    1            11  01_unit/std/improved/serialize_error_spec.spl
    1            11  01_unit/std/improved/serialize_integration_spec.spl
    1            11  01_unit/std/improved/serialize_unit_spec.spl
    1            11  01_unit/std/improved/set_edge_spec.spl
    1            11  01_unit/std/improved/set_error_spec.spl
    1            11  01_unit/std/improved/set_integration_spec.spl
    1            11  01_unit/std/improved/set_unit_spec.spl
    1            11  01_unit/std/improved/signal_edge_spec.spl
    1            11  01_unit/std/improved/signal_error_spec.spl
    1            11  01_unit/std/improved/signal_integration_spec.spl
    1            11  01_unit/std/improved/signal_unit_spec.spl
    1            11  01_unit/std/improved/slice_edge_spec.spl
    1            11  01_unit/std/improved/slice_error_spec.spl
    1            11  01_unit/std/improved/slice_integration_spec.spl
    1            11  01_unit/std/improved/slice_unit_spec.spl
    1            11  01_unit/std/improved/socket_edge_spec.spl
    1            11  01_unit/std/improved/socket_error_spec.spl
    1            11  01_unit/std/improved/socket_integration_spec.spl
    1            11  01_unit/std/improved/socket_unit_spec.spl
    1            11  01_unit/std/improved/sort_edge_spec.spl
    1            11  01_unit/std/improved/sort_error_spec.spl
    1            11  01_unit/std/improved/sort_integration_spec.spl
    1            11  01_unit/std/improved/sort_unit_spec.spl
    1            11  01_unit/std/improved/spawn_edge_spec.spl
    1            11  01_unit/std/improved/spawn_error_spec.spl
    1            11  01_unit/std/improved/spawn_integration_spec.spl
    1            11  01_unit/std/improved/spawn_unit_spec.spl
    1            11  01_unit/std/improved/spec_edge_spec.spl
    1            11  01_unit/std/improved/spec_error_spec.spl
    1            11  01_unit/std/improved/spec_integration_spec.spl
    1            11  01_unit/std/improved/spec_unit_spec.spl
    1            11  01_unit/std/improved/spy_edge_spec.spl
    1            11  01_unit/std/improved/spy_error_spec.spl
    1            11  01_unit/std/improved/spy_integration_spec.spl
    1            11  01_unit/std/improved/spy_unit_spec.spl
    1            11  01_unit/std/improved/stack_edge_spec.spl
    1            11  01_unit/std/improved/stack_error_spec.spl
    1            11  01_unit/std/improved/stack_integration_spec.spl
    1            11  01_unit/std/improved/stack_unit_spec.spl
    1            11  01_unit/std/improved/stdio_edge_spec.spl
    1            11  01_unit/std/improved/stdio_error_spec.spl
    1            11  01_unit/std/improved/stdio_integration_spec.spl
    1            11  01_unit/std/improved/stdio_unit_spec.spl
    1            11  01_unit/std/improved/stream_edge_spec.spl
    1            11  01_unit/std/improved/stream_error_spec.spl
    1            11  01_unit/std/improved/stream_integration_spec.spl
    1            11  01_unit/std/improved/stream_unit_spec.spl
    1            11  01_unit/std/improved/string_edge_spec.spl
    1            11  01_unit/std/improved/string_error_spec.spl
    1            11  01_unit/std/improved/string_integration_spec.spl
    1            11  01_unit/std/improved/string_unit_spec.spl
    1            11  01_unit/std/improved/stub_edge_spec.spl
    1            11  01_unit/std/improved/stub_error_spec.spl
    1            11  01_unit/std/improved/stub_integration_spec.spl
    1            11  01_unit/std/improved/stub_unit_spec.spl
    1            11  01_unit/std/improved/task_edge_spec.spl
    1            11  01_unit/std/improved/task_error_spec.spl
    1            11  01_unit/std/improved/task_integration_spec.spl
    1            11  01_unit/std/improved/task_unit_spec.spl
    1            11  01_unit/std/improved/tcp_edge_spec.spl
    1            11  01_unit/std/improved/tcp_error_spec.spl
    1            11  01_unit/std/improved/tcp_integration_spec.spl
    1            11  01_unit/std/improved/tcp_unit_spec.spl
    1            11  01_unit/std/improved/test_edge_spec.spl
    1            11  01_unit/std/improved/test_error_spec.spl
    1            11  01_unit/std/improved/test_integration_spec.spl
    1            11  01_unit/std/improved/test_unit_spec.spl
    1            11  01_unit/std/improved/thread_edge_spec.spl
    1            11  01_unit/std/improved/thread_error_spec.spl
    1            11  01_unit/std/improved/thread_integration_spec.spl
    1            11  01_unit/std/improved/thread_unit_spec.spl
    1            11  01_unit/std/improved/time_edge_spec.spl
    1            11  01_unit/std/improved/time_error_spec.spl
    1            11  01_unit/std/improved/time_integration_spec.spl
    1            11  01_unit/std/improved/time_unit_spec.spl
    1            11  01_unit/std/improved/trace_edge_spec.spl
    1            11  01_unit/std/improved/trace_error_spec.spl
    1            11  01_unit/std/improved/trace_integration_spec.spl
    1            11  01_unit/std/improved/trace_unit_spec.spl
    1            11  01_unit/std/improved/tuple_edge_spec.spl
    1            11  01_unit/std/improved/tuple_error_spec.spl
    1            11  01_unit/std/improved/tuple_integration_spec.spl
    1            11  01_unit/std/improved/tuple_unit_spec.spl
    1            11  01_unit/std/improved/udp_edge_spec.spl
    1            11  01_unit/std/improved/udp_error_spec.spl
    1            11  01_unit/std/improved/udp_integration_spec.spl
    1            11  01_unit/std/improved/udp_unit_spec.spl
    1            11  01_unit/std/improved/uri_edge_spec.spl
    1            11  01_unit/std/improved/uri_error_spec.spl
    1            11  01_unit/std/improved/uri_integration_spec.spl
    1            11  01_unit/std/improved/uri_unit_spec.spl
    1            11  01_unit/std/improved/url_edge_spec.spl
    1            11  01_unit/std/improved/url_error_spec.spl
    1            11  01_unit/std/improved/url_integration_spec.spl
    1            11  01_unit/std/improved/url_unit_spec.spl
    1            11  01_unit/std/improved/uuid_edge_spec.spl
    1            11  01_unit/std/improved/uuid_error_spec.spl
    1            11  01_unit/std/improved/uuid_integration_spec.spl
    1            11  01_unit/std/improved/uuid_unit_spec.spl
    1            11  01_unit/std/improved/validate_edge_spec.spl
    1            11  01_unit/std/improved/validate_error_spec.spl
    1            11  01_unit/std/improved/validate_integration_spec.spl
    1            11  01_unit/std/improved/validate_unit_spec.spl
    1            11  01_unit/std/improved/vector_edge_spec.spl
    1            11  01_unit/std/improved/vector_error_spec.spl
    1            11  01_unit/std/improved/vector_integration_spec.spl
    1            11  01_unit/std/improved/vector_unit_spec.spl
    1            11  01_unit/std/improved/writer_edge_spec.spl
    1            11  01_unit/std/improved/writer_error_spec.spl
    1            11  01_unit/std/improved/writer_integration_spec.spl
    1            11  01_unit/std/improved/writer_unit_spec.spl
    1            11  01_unit/std/improved/xml_edge_spec.spl
    1            11  01_unit/std/improved/xml_error_spec.spl
    1            11  01_unit/std/improved/xml_integration_spec.spl
    1            11  01_unit/std/improved/xml_unit_spec.spl
    1            11  02_integration/stats_command_spec.spl
    1            10  01_unit/lib/viz/aggregator_walker_spec.spl
    1            10  03_system/feature/usage/gpu_kernels_spec.spl
    1            10  feature/usage/gpu_kernels_spec.spl
    1             9  01_unit/browser_engine/net/cors_spec.spl
    1             9  02_integration/lib/gpu/gpu_kernel_emission_spec.spl
    1             9  shared/core/arithmetic_spec.spl
    1             8  01_unit/lib/viz/damage_spec.spl
    1             8  01_unit/test_runner/tag_parsing_spec.spl
    1             8  02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl
    1             8  03_system/feature/features/mixin_generic_spec.spl
    1             8  03_system/feature/features/mixin_type_inference_spec.spl
    1             8  03_system/feature/usage/context_blocks_spec.spl
    1             8  03_system/feature/usage/math_language_spec.spl
    1             8  feature/usage/context_blocks_spec.spl
    1             8  feature/usage/math_language_spec.spl
    1             8  system/features/mixin_generic_spec.spl
    1             8  system/features/mixin_type_inference_spec.spl
    1             7  01_unit/app/lsp/protocol_types_spec.spl
    1             7  02_integration/t32_hw/backends/config_file_spec.spl
    1             7  02_integration/t32_hw/backends/ctypes_spec.spl
    1             7  02_integration/t32_hw/backends/tNrem_spec.spl
    1             7  03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl
    1             7  03_system/feature/features/collections_system_spec.spl
    1             7  03_system/feature/features/error_handling_system_spec.spl
    1             7  03_system/feature/features/serialization_system_spec.spl
    1             7  03_system/feature/features/string_system_spec.spl
    1             7  03_system/feature/usage/macro_validation_spec.spl
    1             7  03_system/feature/web_platform/css/animations_wpt_spec.spl
    1             7  03_system/infrastructure/build_system_spec.spl
    1             7  03_system/infrastructure/cli_system_spec.spl
    1             7  03_system/infrastructure/config_system_spec.spl
    1             7  03_system/infrastructure/debugging_system_spec.spl
    1             7  03_system/infrastructure/formatter_system_spec.spl
    1             7  03_system/infrastructure/jj_system_spec.spl
    1             7  03_system/infrastructure/logging_system_spec.spl
    1             7  03_system/infrastructure/profiling_system_spec.spl
    1             7  03_system/infrastructure/test_runner_system_spec.spl
    1             7  03_system/os/filesystem_system_spec.spl
    1             7  03_system/os/io_system_spec.spl
    1             7  03_system/os/network_system_spec.spl
    1             7  03_system/os/path_system_spec.spl
    1             7  03_system/os/process_system_spec.spl
    1             7  03_system/stdlib/math/math_system_spec.spl
    1             7  03_system/tools/lint/linter_system_spec.spl
    1             7  03_system/tools/mcp/mcp_system_spec.spl
    1             7  feature/usage/macro_validation_spec.spl
    1             7  system/features/collections_system_spec.spl
    1             7  system/features/error_handling_system_spec.spl
    1             7  system/features/serialization_system_spec.spl
    1             7  system/features/string_system_spec.spl
    1             7  system/lint/linter_system_spec.spl
    1             7  system/math/math_system_spec.spl
    1             7  system/mcp/mcp_system_spec.spl
    1             7  system/module_import/import_system_spec.spl
    1             6  01_unit/app/build_coverage_spec.spl
    1             6  01_unit/app/test_runner_coverage_spec.spl
    1             6  01_unit/app/utils/colors_spec.spl
    1             6  01_unit/lib/database_coverage_spec.spl
    1             6  01_unit/lib/common/color/color_parse_spec.spl
    1             6  02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl
    1             6  02_integration/os/port/disk_image_bake_spec.spl
    1             6  03_system/feature/usage/contract_persistence_feature_spec.spl
    1             6  03_system/feature/usage/effect_system_spec.spl
    1             6  03_system/feature/usage/operators_advanced_spec.spl
    1             6  03_system/feature/usage/trait_coherence_spec.spl
    1             6  03_system/os/port/eNe_qemu_smoke_spec.spl
    1             6  03_system/os/port/fork_exec_spec.spl
    1             6  05_perf/browser/simple_web_browser_engine_production_budget_spec.spl
    1             6  feature/usage/contract_persistence_feature_spec.spl
    1             6  feature/usage/effect_system_spec.spl
    1             6  feature/usage/operators_advanced_spec.spl
    1             6  feature/usage/trait_coherence_spec.spl
    1             5  01_unit/common/structural/mapping_contract_spec.spl
    1             5  01_unit/lib/common/string_literals_spec.spl
    1             5  01_unit/lib/extended/collections_graph_integration_spec.spl
    1             5  01_unit/lib/extended/collections_graph_unit_spec.spl
    1             5  01_unit/lib/extended/collections_heap_integration_spec.spl
    1             5  01_unit/lib/extended/collections_heap_unit_spec.spl
    1             5  01_unit/lib/extended/collections_tree_integration_spec.spl
    1             5  01_unit/lib/extended/collections_tree_unit_spec.spl
    1             5  01_unit/lib/extended/collections_trie_integration_spec.spl
    1             5  01_unit/lib/extended/collections_trie_unit_spec.spl
    1             5  01_unit/lib/extended/cuda_device_integration_spec.spl
    1             5  01_unit/lib/extended/cuda_device_unit_spec.spl
    1             5  01_unit/lib/extended/cuda_event_integration_spec.spl
    1             5  01_unit/lib/extended/cuda_event_unit_spec.spl
    1             5  01_unit/lib/extended/cuda_kernel_integration_spec.spl
    1             5  01_unit/lib/extended/cuda_kernel_unit_spec.spl
    1             5  01_unit/lib/extended/cuda_stream_integration_spec.spl
    1             5  01_unit/lib/extended/cuda_stream_unit_spec.spl
    1             5  01_unit/lib/extended/execution_context_integration_spec.spl
    1             5  01_unit/lib/extended/execution_context_unit_spec.spl
    1             5  01_unit/lib/extended/execution_fiber_integration_spec.spl
    1             5  01_unit/lib/extended/execution_fiber_unit_spec.spl
    1             5  01_unit/lib/extended/execution_task_integration_spec.spl
    1             5  01_unit/lib/extended/execution_task_unit_spec.spl
    1             5  01_unit/lib/extended/execution_thread_integration_spec.spl
    1             5  01_unit/lib/extended/execution_thread_unit_spec.spl
    1             5  01_unit/lib/extended/gpu_buffer_integration_spec.spl
    1             5  01_unit/lib/extended/gpu_buffer_unit_spec.spl
    1             5  01_unit/lib/extended/gpu_compute_integration_spec.spl
    1             5  01_unit/lib/extended/gpu_compute_unit_spec.spl
    1             5  01_unit/lib/extended/gpu_pipeline_integration_spec.spl
    1             5  01_unit/lib/extended/gpu_pipeline_unit_spec.spl
    1             5  01_unit/lib/extended/gpu_render_integration_spec.spl
    1             5  01_unit/lib/extended/gpu_render_unit_spec.spl
    1             5  01_unit/lib/extended/gpu_shader_integration_spec.spl
    1             5  01_unit/lib/extended/gpu_shader_unit_spec.spl
    1             5  01_unit/lib/extended/hooks_after_integration_spec.spl
    1             5  01_unit/lib/extended/hooks_after_unit_spec.spl
    1             5  01_unit/lib/extended/hooks_around_integration_spec.spl
    1             5  01_unit/lib/extended/hooks_around_unit_spec.spl
    1             5  01_unit/lib/extended/hooks_before_integration_spec.spl
    1             5  01_unit/lib/extended/hooks_before_unit_spec.spl
    1             5  01_unit/lib/extended/hooks_error_integration_spec.spl
    1             5  01_unit/lib/extended/hooks_error_unit_spec.spl
    1             5  01_unit/lib/extended/pure_function_integration_spec.spl
    1             5  01_unit/lib/extended/pure_function_unit_spec.spl
    1             5  01_unit/lib/extended/pure_immutable_integration_spec.spl
    1             5  01_unit/lib/extended/pure_immutable_unit_spec.spl
    1             5  01_unit/lib/extended/pure_persistent_integration_spec.spl
    1             5  01_unit/lib/extended/pure_persistent_unit_spec.spl
    1             5  01_unit/lib/extended/qemu_device_integration_spec.spl
    1             5  01_unit/lib/extended/qemu_device_unit_spec.spl
    1             5  01_unit/lib/extended/qemu_system_integration_spec.spl
    1             5  01_unit/lib/extended/qemu_system_unit_spec.spl
    1             5  01_unit/lib/extended/qemu_user_integration_spec.spl
    1             5  01_unit/lib/extended/qemu_user_unit_spec.spl
    1             5  01_unit/lib/extended/torch_data_integration_spec.spl
    1             5  01_unit/lib/extended/torch_data_unit_spec.spl
    1             5  01_unit/lib/extended/torch_loss_integration_spec.spl
    1             5  01_unit/lib/extended/torch_loss_unit_spec.spl
    1             5  01_unit/lib/extended/torch_nn_integration_spec.spl
    1             5  01_unit/lib/extended/torch_nn_unit_spec.spl
    1             5  01_unit/lib/extended/torch_optim_integration_spec.spl
    1             5  01_unit/lib/extended/torch_optim_unit_spec.spl
    1             5  01_unit/lib/extended/torch_tensor_integration_spec.spl
    1             5  01_unit/lib/extended/torch_tensor_unit_spec.spl
    1             5  02_integration/storage/dbfs/dbfs_no_regression_spec.spl
    1             5  02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl
    1             5  03_system/feature/app/easy_fix_rules_spec.spl
    1             5  03_system/feature/features/traits/trait_coherence_spec.spl
    1             5  03_system/feature/usage/concurrency_primitives_spec.spl
    1             5  03_system/feature/usage/enums_spec.spl
    1             5  03_system/feature/usage/generics_advanced_spec.spl
    1             5  03_system/os/wm/simple_wm_render_provenance_spec.spl
    1             5  feature/usage/concurrency_primitives_spec.spl
    1             5  feature/usage/enums_spec.spl
    1             5  feature/usage/generics_advanced_spec.spl
    1             5  feature/web_platform/css/at_supports_wpt_spec.spl
    1             5  system/features/traits/trait_coherence_spec.spl
    1             4  01_unit/app/extended/aggregate_basic_spec.spl
    1             4  01_unit/app/extended/analyze_basic_spec.spl
    1             4  01_unit/app/extended/apply_basic_spec.spl
    1             4  01_unit/app/extended/backup_basic_spec.spl
    1             4  01_unit/app/extended/benchmark_basic_spec.spl
    1             4  01_unit/app/extended/bundle_basic_spec.spl
    1             4  01_unit/app/extended/chart_basic_spec.spl
    1             4  01_unit/app/extended/check_deps_basic_spec.spl
    1             4  01_unit/app/extended/check_lint_basic_spec.spl
    1             4  01_unit/app/extended/check_types_basic_spec.spl
    1             4  01_unit/app/extended/clean_basic_spec.spl
    1             4  01_unit/app/extended/clone_basic_spec.spl
    1             4  01_unit/app/extended/combine_basic_spec.spl
    1             4  01_unit/app/extended/compare_basic_spec.spl
    1             4  01_unit/app/extended/compress_tool_basic_spec.spl
    1             4  01_unit/app/extended/convert_basic_spec.spl
    1             4  01_unit/app/extended/create_basic_spec.spl
    1             4  01_unit/app/extended/decompress_basic_spec.spl
    1             4  01_unit/app/extended/deploy_basic_spec.spl
    1             4  01_unit/app/extended/destroy_basic_spec.spl
    1             4  01_unit/app/extended/diagram_basic_spec.spl
    1             4  01_unit/app/extended/diff_tool_basic_spec.spl
    1             4  01_unit/app/extended/downgrade_basic_spec.spl
    1             4  01_unit/app/extended/expand_basic_spec.spl
    1             4  01_unit/app/extended/explore_basic_spec.spl
    1             4  01_unit/app/extended/export_basic_spec.spl
    1             4  01_unit/app/extended/extract_basic_spec.spl
    1             4  01_unit/app/extended/filter_basic_spec.spl
    1             4  01_unit/app/extended/generate_basic_spec.spl
    1             4  01_unit/app/extended/graph_basic_spec.spl
    1             4  01_unit/app/extended/group_basic_spec.spl
    1             4  01_unit/app/extended/health_basic_spec.spl
    1             4  01_unit/app/extended/import_basic_spec.spl
    1             4  01_unit/app/extended/inflate_basic_spec.spl
    1             4  01_unit/app/extended/inspect_basic_spec.spl
    1             4  01_unit/app/extended/join_basic_spec.spl
    1             4  01_unit/app/extended/merge_basic_spec.spl
    1             4  01_unit/app/extended/merge_tool_basic_spec.spl
    1             4  01_unit/app/extended/migrate_basic_spec.spl
    1             4  01_unit/app/extended/minify_basic_spec.spl
    1             4  01_unit/app/extended/monitor_basic_spec.spl
    1             4  01_unit/app/extended/optimize_basic_spec.spl
    1             4  01_unit/app/extended/pack_basic_spec.spl
    1             4  01_unit/app/extended/patch_basic_spec.spl
    1             4  01_unit/app/extended/plot_basic_spec.spl
    1             4  01_unit/app/extended/query_basic_spec.spl
    1             4  01_unit/app/extended/redo_basic_spec.spl
    1             4  01_unit/app/extended/refactor_basic_spec.spl
    1             4  01_unit/app/extended/report_basic_spec.spl
    1             4  01_unit/app/extended/reset_basic_spec.spl
    1             4  01_unit/app/extended/restart_basic_spec.spl
    1             4  01_unit/app/extended/restore_basic_spec.spl
    1             4  01_unit/app/extended/revert_basic_spec.spl
    1             4  01_unit/app/extended/rollback_basic_spec.spl
    1             4  01_unit/app/extended/scaffold_basic_spec.spl
    1             4  01_unit/app/extended/separate_basic_spec.spl
    1             4  01_unit/app/extended/serve_basic_spec.spl
    1             4  01_unit/app/extended/snapshot_basic_spec.spl
    1             4  01_unit/app/extended/sort_basic_spec.spl
    1             4  01_unit/app/extended/split_basic_spec.spl
    1             4  01_unit/app/extended/start_basic_spec.spl
    1             4  01_unit/app/extended/status_basic_spec.spl
    1             4  01_unit/app/extended/stop_basic_spec.spl
    1             4  01_unit/app/extended/summarize_basic_spec.spl
    1             4  01_unit/app/extended/sync_basic_spec.spl
    1             4  01_unit/app/extended/template_basic_spec.spl
    1             4  01_unit/app/extended/trace_basic_spec.spl
    1             4  01_unit/app/extended/transform_basic_spec.spl
    1             4  01_unit/app/extended/undo_basic_spec.spl
    1             4  01_unit/app/extended/unpack_basic_spec.spl
    1             4  01_unit/app/extended/upgrade_basic_spec.spl
    1             4  01_unit/app/extended/validate_basic_spec.spl
    1             4  01_unit/app/extended/visualize_basic_spec.spl
    1             4  01_unit/app/extended/watch_basic_spec.spl
    1             4  01_unit/app/tooling/url_utils_spec.spl
    1             4  01_unit/common/structural/identity_tagmap_contract_spec.spl
    1             4  01_unit/lib/common/shared_examples_spec.spl
    1             4  01_unit/lib/common/units/units_spec.spl
    1             4  01_unit/os/hosted/hosted_browser_renderer_policy_spec.spl
    1             4  01_unit/std/shared_examples_spec.spl
    1             4  02_integration/rendering/wm_perf_spec.spl
    1             4  03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl
    1             4  03_system/feature/app/config_env_spec.spl
    1             4  03_system/feature/features/with_statement_basic_spec.spl
    1             4  03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl
    1             4  03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl
    1             4  03_system/feature/usage/stackless_coroutines_spec.spl
    1             4  feature/usage/hm_type_inference_spec.spl
    1             4  feature/usage/stackless_coroutines_spec.spl
    1             4  feature/web_platform/css/custom_properties_wpt_spec.spl
    1             4  system/features/with_statement_basic_spec.spl
    1             4  system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl
    1             4  system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl
    1             3  01_unit/app/test_analysis_spec.spl
    1             3  01_unit/app/tooling/baseNutils_spec.spl
    1             3  01_unit/app/tooling/basic_spec.spl
    1             3  01_unit/app/tooling/compile_commands_spec.spl
    1             3  01_unit/app/tooling/coverage_spec.spl
    1             3  01_unit/app/tooling/iNn_commands_spec.spl
    1             3  01_unit/app/tooling/misc_commands_spec.spl
    1             3  01_unit/app/tooling/pkg_commands_spec.spl
    1             3  01_unit/app/tooling/time_utils_spec.spl
    1             3  01_unit/app/tooling/web_commands_spec.spl
    1             3  01_unit/browser_engine/browser_renderer_spec.spl
    1             3  01_unit/common/structural/clang_contract_spec.spl
    1             3  01_unit/lib/common/perf_optimization_spec.spl
    1             3  01_unit/lib/compositor/stacking_renorm_spec.spl
    1             3  01_unit/lib/engine/destruction_spec.spl
    1             3  01_unit/lib/ml/autograd_spec.spl
    1             3  01_unit/lib/ml/linalg_spec.spl
    1             3  01_unit/os/kernel/scheduler/scheduler_spec.spl
    1             3  01_unit/os/shell/awk_spec.spl
    1             3  01_unit/std/perf_optimization_spec.spl
    1             3  03_system/engine/gameNd_hello_demo_spec.spl
    1             3  03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl
    1             3  03_system/feature/usage/macros_spec.spl
    1             3  03_system/feature/usage/method_missing_spec.spl
    1             3  03_system/feature/web_platform/css/transforms_wpt_spec.spl
    1             3  03_system/generated/simple_nesting_spec.spl
    1             3  03_system/tools/llm/claude_full/bridge/bridgeMessaging_spec.spl
    1             3  03_system/tools/llm/claude_full/services/api/withRetry_spec.spl
    1             3  03_system/tools/llm/claude_full/services/mcp/client_spec.spl
    1             3  05_perf/bench/db_benchmark_suite_spec.spl
    1             3  feature/usage/aop_spec.spl
    1             3  feature/usage/macros_spec.spl
    1             3  feature/usage/method_missing_spec.spl
    1             3  perf/bench/db_benchmark_suite_spec.spl
    1             3  shared/core/primitives_spec.spl
    1             3  system/gameNd_hello_demo_spec.spl
    1             3  system/features/ui_structural_patchset/ui_structural_patchset_spec.spl
    1             2  01_unit/app/complete/addNcomplete_spec.spl
    1             2  01_unit/app/complete/auditNcomplete_spec.spl
    1             2  01_unit/app/complete/buildNcomplete_spec.spl
    1             2  01_unit/app/complete/checkNcomplete_spec.spl
    1             2  01_unit/app/complete/cliNcomplete_spec.spl
    1             2  01_unit/app/complete/compileNcomplete_spec.spl
    1             2  01_unit/app/complete/coverageNcomplete_spec.spl
    1             2  01_unit/app/complete/debugNcomplete_spec.spl
    1             2  01_unit/app/complete/docNcomplete_spec.spl
    1             2  01_unit/app/complete/fixNcomplete_spec.spl
    1             2  01_unit/app/complete/fmtNcomplete_spec.spl
    1             2  01_unit/app/complete/infoNcomplete_spec.spl
    1             2  01_unit/app/complete/initNcomplete_spec.spl
    1             2  01_unit/app/complete/installNcomplete_spec.spl
    1             2  01_unit/app/complete/lintNcomplete_spec.spl
    1             2  01_unit/app/complete/packageNcomplete_spec.spl
    1             2  01_unit/app/complete/profileNcomplete_spec.spl
    1             2  01_unit/app/complete/publishNcomplete_spec.spl
    1             2  01_unit/app/complete/releaseNcomplete_spec.spl
    1             2  01_unit/app/complete/runNcomplete_spec.spl
    1             2  01_unit/app/complete/searchNcomplete_spec.spl
    1             2  01_unit/app/complete/statsNcomplete_spec.spl
    1             2  01_unit/app/complete/testNcomplete_spec.spl
    1             2  01_unit/app/complete/treeNcomplete_spec.spl
    1             2  01_unit/app/complete/updateNcomplete_spec.spl
    1             2  01_unit/app/mcp_unit/mcp_jsonrpc_spec.spl
    1             2  01_unit/app/mcp_unit/ui_access_tools_spec.spl
    1             2  01_unit/app/ui/ui_access_store_spec.spl
    1             2  01_unit/browser_engine/htmlNlib_tokenizer_spec.spl
    1             2  01_unit/lib/log_export_spec.spl
    1             2  01_unit/lib/common/compress_framework_spec.spl
    1             2  01_unit/lib/common/decorators_comprehensive_spec.spl
    1             2  01_unit/lib/common/log_export_spec.spl
    1             2  01_unit/lib/common/web/browser_session_context_spec.spl
    1             2  01_unit/lib/engine/resource_handle_spec.spl
    1             2  01_unit/lib/std/time_spec.spl
    1             2  01_unit/lib/viz/frame_scheduler_spec.spl
    1             2  01_unit/os/apps/editor/editor_spec.spl
    1             2  01_unit/os/sosix/queue_notify_spec.spl
    1             2  01_unit/spec/package_unfold_spec.spl
    1             2  01_unit/std/decorators_comprehensive_spec.spl
    1             2  01_unit/std/http_client/url_parse_spec.spl
    1             2  02_integration/lib/failsafe_integration_spec.spl
    1             2  03_system/app/os/feature/engineNd_qemu_spec.spl
    1             2  03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl
    1             2  03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl
    1             2  03_system/engine/gameNd_input_snapshot_spec.spl
    1             2  03_system/feature/features/baremetal/interrupt_spec.spl
    1             2  03_system/feature/usage/hm_type_inference_spec.spl
    1             2  03_system/feature/usage/minimal_spec.spl
    1             2  03_system/feature/usage/primitive_types_spec.spl
    1             2  03_system/generated/medium_nesting_spec.spl
    1             2  03_system/hardware/t32_tools/tNgui_system_spec.spl
    1             2  03_system/infrastructure/smoke/compile_smoke_spec.spl
    1             2  03_system/tools/llm/claude_full/bridge/bridgeMain_spec.spl
    1             2  05_perf/web/web_server_bench_spec.spl
    1             2  feature/usage/minimal_spec.spl
    1             2  feature/usage/primitive_types_spec.spl
    1             2  system/gameNd_input_snapshot_spec.spl
    1             2  system/features/baremetal/interrupt_spec.spl
    1             2  system/smoke/compile_smoke_spec.spl
    1             2  system/t32_tools/tNgui_system_spec.spl
    2             2  01_unit/lib/common/mock_phaseNspec.spl
    1             1  01_unit/app/devhub/cmd_daily_debug_spec.spl
    1             1  01_unit/app/llm_caret/chat_tui_input_spec.spl
    1             1  01_unit/app/llm_caret/main_spec.spl
    1             1  01_unit/app/mcp_t32/mcp_tNwsl_wrapper_spec.spl
    1             1  01_unit/app/meta/comment_only_spec.spl
    1             1  01_unit/app/svim/core_spec.spl
    1             1  01_unit/app/tooling/csv_utils_spec.spl
    1             1  01_unit/app/tooling/env_commands_spec.spl
    1             1  01_unit/app/tooling/extract_tests_spec.spl
    1             1  01_unit/app/tooling/feature_db_spec.spl
    1             1  01_unit/app/tooling/file_walker_spec.spl
    1             1  01_unit/app/tooling/fix_if_val_pattern_spec.spl
    1             1  01_unit/app/tooling/lint_config_spec.spl
    1             1  01_unit/app/tooling/migrate_me_syntax_spec.spl
    1             1  01_unit/app/tooling/migrate_spec_to_spl_spec.spl
    1             1  01_unit/app/tooling/migrate_val_var_spec.spl
    1             1  01_unit/app/tooling/remove_self_params_spec.spl
    1             1  01_unit/app/tooling/scaffold_feature_spec.spl
    1             1  01_unit/app/tooling/spec_gen_spec.spl
    1             1  01_unit/app/tooling/startup_spec.spl
    1             1  01_unit/app/tooling/test_db_serializer_spec.spl
    1             1  01_unit/browser_engine/script/script_host_spec.spl
    1             1  01_unit/bugs/text_bracket_slice_byte_index_spec.spl
    1             1  01_unit/language/nil_presence_idioms_spec.spl
    1             1  01_unit/lib/common/error_handling_spec.spl
    1             1  01_unit/lib/common/regex_char_utils_coverage_spec.spl
    1             1  01_unit/lib/common/serialization_primitives_spec.spl
    1             1  01_unit/lib/common/skip_ignore_integration_spec.spl
    1             1  01_unit/lib/common/string_core_basic_coverage_spec.spl
    1             1  01_unit/lib/common/string_core_charcode_spec.spl
    1             1  01_unit/lib/common/string_spec.spl
    1             1  01_unit/lib/common/feature_validation/testing_framework_spec.spl
    1             1  01_unit/lib/common/markdown/markdown_visual_editor_spec.spl
    1             1  01_unit/lib/common/ui/wm_window_state_spec.spl
    1             1  01_unit/lib/common/web/browser_session_form_spec.spl
    1             1  01_unit/lib/common/web/browser_session_url_spec.spl
    1             1  01_unit/lib/database/database_feature_utils_spec.spl
    1             1  01_unit/lib/editor/document_service_spec.spl
    1             1  01_unit/lib/engine/gpu_bridge_spec.spl
    1             1  01_unit/lib/engine/scene_node_spec.spl
    1             1  01_unit/lib/engine/shader_graph_spec.spl
    1             1  01_unit/lib/engine/sprite_spec.spl
    1             1  01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl
    1             1  01_unit/lib/hardware/vhdl_gen/rvNtrap_completeness_spec.spl
    1             1  01_unit/lib/ml/engine_spec.spl
    1             1  01_unit/lib/std/file/file_io_spec.spl
    1             1  01_unit/os/apps/file_manager/file_manager_spec.spl
    1             1  01_unit/os/apps/shell/shell_app_spec.spl
    1             1  01_unit/os/compositor/wm_scene_spec.spl
    1             1  01_unit/os/hosted/hosted_browser_renderer_worker_spec.spl
    1             1  01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl
    1             1  01_unit/os/shell/shell_starship_modules_spec.spl
    1             1  01_unit/os/shell/shell_starship_spec.spl
    1             1  01_unit/spec/expect_bool_spec.spl
    2             1  01_unit/std/mock_phaseNspec.spl
    1             1  01_unit/std/skip_ignore_integration_spec.spl
    1             1  01_unit/tools/desktop/markdown_visual_editor_spec.spl
    1             1  01_unit/tools/shell/file_spec.spl
   10             1  02_integration/e2e/build_test_integrationNspec.spl
   10             1  02_integration/e2e/compile_run_integrationNspec.spl
   10             1  02_integration/e2e/debug_trace_integrationNspec.spl
   10             1  02_integration/e2e/error_report_integrationNspec.spl
    1             1  02_integration/e2e/full_compilation_pipelineNspec.spl
    1             1  02_integration/e2e/full_test_pipelineNspec.spl
   10             1  02_integration/e2e/import_resolve_integrationNspec.spl
   10             1  02_integration/e2e/lint_fix_integrationNspec.spl
   10             1  02_integration/e2e/package_publish_integrationNspec.spl
   10             1  02_integration/e2e/profile_optimize_integrationNspec.spl
    1             1  02_integration/rendering/browser_session_dom_input_spec.spl
    1             1  02_integration/rendering/web_layout_cuda_live_spec.spl
    1             1  02_integration/rust/meta/comment_only_spec.spl
    1             1  02_integration/storage/dbfs/arena_as_blob_backend_spec.spl
    1             1  02_integration/t32_hw/Nscreenshot_spec.spl
    1             1  03_system/app/browser/feature/browser_input_button_keyboard_activation_spec.spl
    1             1  03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl
    1             1  03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl
    1             1  03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl
    1             1  03_system/engine/gameNd_archtest_spec.spl
    1             1  03_system/engine/gameNd_canvas_api_spec.spl
    1             1  03_system/engine/gameNd_cli_spec.spl
    1             1  03_system/engine/gameNd_sdn_assets_spec.spl
    1             1  03_system/feature/features/baremetal/static_assert_spec.spl
    1             1  03_system/feature/language/modules_spec.spl
    1             1  03_system/feature/usage/context_managers_spec.spl
    1             1  03_system/feature/usage/indentation_blocks_spec.spl
    1             1  03_system/feature/usage/multiline_syntax_spec.spl
    1             1  03_system/feature/usage/no_paren_calls_spec.spl
    1             1  03_system/feature/usage/tensor_spec.spl
    1             1  03_system/feature/usage/union_types_spec.spl
    1             1  03_system/feature/usage/unit_types_spec.spl
    1             1  03_system/feature/usage/visibility_modifiers_spec.spl
    1             1  03_system/feature/web_platform/css/custom_properties_wpt_spec.spl
    1             1  03_system/feature/web_platform/html/html_parsing_contexts_spec.spl
    1             1  03_system/generated/bdd_timeout_minimal_spec.spl
    1             1  03_system/generated/deep_nesting_spec.spl
    1             1  03_system/generated/empty_spec.spl
    1             1  03_system/generated/gherkin_spec.spl
    1             1  03_system/generated/simple_nested_spec.spl
    1             1  03_system/generated/stressNsystem_spec.spl
    1             1  03_system/gpu/metal_backend_mac_host_spec.spl
    1             1  03_system/gui/editor_keybinding_spec.spl
    1             1  03_system/os/port/alt_rootfs_disk_boot_spec.spl
    1             1  03_system/os/port/disk_boot_spec.spl
    1             1  03_system/os/port/phaseNeNe_spec.spl
    1             1  03_system/os/port/rustc_static_eNe_spec.spl
    1             1  03_system/os/port/xNNelf_load_spec.spl
    1             1  03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl
    1             1  03_system/tools/lsp/lsp_spec.spl
    1             1  05_perf/db/db_ram_vs_persistent_bench_spec.spl
    1             1  05_perf/os/os_fs_sched_bench_spec.spl
    1             1  feature/usage/context_managers_spec.spl
    1             1  feature/usage/indentation_blocks_spec.spl
    1             1  feature/usage/multiline_syntax_spec.spl
    1             1  feature/usage/no_paren_calls_spec.spl
    1             1  feature/usage/null_coalescing_try_operator_spec.spl
    1             1  feature/usage/tensor_spec.spl
    1             1  feature/usage/union_types_spec.spl
    1             1  feature/usage/unit_types_spec.spl
    1             1  feature/usage/visibility_modifiers_spec.spl
    1             1  shared/control_flow/static_fn_spec.spl
    1             1  shared/core/hello_spec.spl
    1             1  shared/core/minimal_spec.spl
    1             1  system/editor_keybinding_spec.spl
    1             1  system/gameNd_archtest_spec.spl
    1             1  system/gameNd_canvas_api_spec.spl
    1             1  system/gameNd_cli_spec.spl
    1             1  system/gameNd_sdn_assets_spec.spl
    1             1  system/features/baremetal/static_assert_spec.spl
    1             1  system/lsp/lsp_spec.spl
    1             0  01_unit/app/renderdoc_replay_inspect_spec.spl
    1             0  01_unit/app/diagram/call_flow_profiling_spec.spl
    1             0  01_unit/app/duplicate_check/duplicate_check_spec.spl
    1             0  01_unit/app/editor/md_toggle_bold_spec.spl
    1             0  01_unit/app/llm_caret/chat_tui_spec.spl
    1             0  01_unit/app/lsp/lsp_visibility_support_spec.spl
    1             0  01_unit/app/mcp_unit/command_filter_spec.spl
    1             0  01_unit/app/mcp_unit/crash_prevention_spec.spl
    1             0  01_unit/app/mcp_unit/dependencies_spec.spl
    1             0  01_unit/app/mcp_unit/error_handler_spec.spl
    1             0  01_unit/app/mcp_unit/export_syntax_spec.spl
    1             0  01_unit/app/mcp_unit/failure_analysis_spec.spl
    1             0  01_unit/app/mcp_unit/mcp_cancellation_spec.spl
    1             0  01_unit/app/mcp_unit/mcp_content_types_spec.spl
    1             0  01_unit/app/mcp_unit/mcp_logging_spec.spl
    1             0  01_unit/app/mcp_unit/mcp_notifications_spec.spl
    1             0  01_unit/app/mcp_unit/mcp_progress_spec.spl
    1             0  01_unit/app/mcp_unit/mcp_roots_spec.spl
    1             0  01_unit/app/mcp_unit/pagination_spec.spl
    1             0  01_unit/app/mcp_unit/prompts_spec.spl
    1             0  01_unit/app/mcp_unit/transport_error_handling_spec.spl
    1             0  01_unit/app/mcp_unit/transport_tcp_spec.spl
    1             0  01_unit/app/test_runner_new/test_categorization_spec.spl
    1             0  01_unit/app/tooling/regex_utils_spec.spl
    1             0  01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl
    1             0  01_unit/app/ui.web/host_taskbar_persistence_spec.spl
    1             0  01_unit/app/ui/access_spec.spl
    1             0  01_unit/browser/script/dom_query_selector_all_linear_spec.spl
    1             0  01_unit/browser_engine/html_tokenizer_abrupt_comment_spec.spl
    1             0  01_unit/browser_engine/html_tokenizer_spec.spl
    1             0  01_unit/browser_engine/html_tree_builder_hardening_spec.spl
    1             0  01_unit/lib/common/completed_animation_handle_capacity_spec.spl
    1             0  01_unit/lib/common/js_async_fetch_spec.spl
    1             0  01_unit/lib/common/js_timer_drain_limit_spec.spl
    1             0  01_unit/lib/common/serialization_exhaustive_spec.spl
    1             0  01_unit/lib/common/compress/compression_utilities_spec.spl
    1             0  01_unit/lib/common/compress/lzNblock_bounds_spec.spl
    1             0  01_unit/lib/common/compress/lzNframe_header_spec.spl
    1             0  01_unit/lib/common/compress/lzmaNchunk_decoder_spec.spl
    1             0  01_unit/lib/common/compress/zstd_bit_writer_bounds_spec.spl
    1             0  01_unit/lib/common/compress/zstd_bits_bounds_spec.spl
    1             0  01_unit/lib/common/compress/zstd_frame_header_spec.spl
    1             0  01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.spl
    1             0  01_unit/lib/common/compress/zstd_fse_forward_bits_spec.spl
    1             0  01_unit/lib/common/compress/zstd_msb_bits_bounds_spec.spl
    1             0  01_unit/lib/common/compress/zstd_sequence_spec.spl
    1             0  01_unit/lib/common/markdown/markdown_spec.spl
    1             0  01_unit/lib/common/text_layout/font_render_config_spec.spl
    1             0  01_unit/lib/common/text_layout/font_renderer_spec.spl
    1             0  01_unit/lib/common/ui/draw_ir_spec.spl
    1             0  01_unit/lib/common/ui/draw_ir_vNbackend_access_spec.spl
    1             0  01_unit/lib/common/ui/host_env_contract_spec.spl
    1             0  01_unit/lib/common/ui/render_surface_widget_spec.spl
    1             0  01_unit/lib/common/web/browser_renderer_protocol_spec.spl
    1             0  01_unit/lib/common/web/browser_session_controls_spec.spl
    1             0  01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl
    1             0  01_unit/lib/common/web/browser_session_http_status_spec.spl
    1             0  01_unit/lib/common/web/browser_session_spec.spl
    1             0  01_unit/lib/common/web/browser_session_storage_spec.spl
    1             0  01_unit/lib/common/web/browser_text_selection_spec.spl
    1             0  01_unit/lib/editor/mcp_session_tools_spec.spl
    1             0  01_unit/lib/gpu/engine3d/font_compat_spec.spl
    1             0  01_unit/lib/std/language/mixin_spec.spl
    1             0  01_unit/lib/std/language/mixin_static_poly_integration_spec.spl
    1             0  01_unit/lib/std/language/static_polymorphism_spec.spl
    1             0  01_unit/os/compositor/armNvirtio_input_backend_spec.spl
    1             0  01_unit/os/compositor/compositor_content_registry_spec.spl
    1             0  01_unit/os/compositor/host_compositor_entry_spec.spl
    1             0  01_unit/os/compositor/host_content_frame_admission_spec.spl
    1             0  01_unit/os/compositor/host_gui_event_router_spec.spl
    1             0  01_unit/os/compositor/simple_web_window_renderer_spec.spl
    1             0  01_unit/os/compositor/wm_aetheric_web_material_spec.spl
    1             0  01_unit/os/desktop/shell_taskbar_pin_spec.spl
    1             0  01_unit/os/desktop/simpleos_wm_queued_input_drain_contract_spec.spl
    1             0  01_unit/os/drivers/real_device_readiness_spec.spl
    1             0  01_unit/os/drivers/audio/hda_controller_spec.spl
    1             0  01_unit/os/hosted/hosted_browser_compositor_revision_route_source_spec.spl
    1             0  01_unit/os/hosted/hosted_browser_renderer_entry_source_spec.spl
    1             0  01_unit/os/kernel/ipc/syscall_spec.spl
    1             0  01_unit/os/multiarch/hal_trait_surface_spec.spl
    1             0  01_unit/os/multiarch/nvfsNbit_layout_spec.spl
    1             0  01_unit/os/port/simpleos_font_bundle_spec.spl
    1             0  01_unit/os/services/llm/ui_access_dispatch_spec.spl
    1             0  01_unit/os/tty/tty_write_delivery_spec.spl
    1             0  01_unit/spec/registry_spec.spl
    1             0  01_unit/std/collections_spec.spl
    1             0  01_unit/std/spec_expect_bool_shortcut_spec.spl
    1             0  02_integration/rvNmulti_backend_boot_spec.spl
    1             0  02_integration/simpleos_self_host_spec.spl
    1             0  02_integration/app/add_remove_log_modes_spec.spl
    1             0  02_integration/app/app_cli_intensive_spec.spl
    1             0  02_integration/app/app_mcp_intensive_spec.spl
    1             0  02_integration/app/cli_run_file_inherited_stdio_spec.spl
    1             0  02_integration/app/io_intensive_spec.spl
    1             0  02_integration/app/loader_run_function_spec.spl
    1             0  02_integration/app/mcp_stdio_integration_spec.spl
    1             0  02_integration/app/spipe_quality_lint_spec.spl
    1             0  02_integration/baremetal/baremetal_build_spec.spl
    1             0  02_integration/baremetal/connection_matrix_qemu_spec.spl
    1             0  02_integration/baremetal/openocd_qemu_arm_spec.spl
    1             0  02_integration/baremetal/remote_riscvNspec.spl
    1             0  02_integration/lib/database_atomic_spec.spl
    1             0  02_integration/lib/database_core_spec.spl
    1             0  02_integration/lib/database_eNe_spec.spl
    1             0  02_integration/lib/database_query_spec.spl
    1             0  02_integration/lib/persistence_intensive_spec.spl
    1             0  02_integration/lib/protocol_intensive_spec.spl
    1             0  02_integration/lib/query_intensive_spec.spl
    1             0  02_integration/lib/simd_stdlib_spec.spl
    1             0  02_integration/lib/stdlib_intensive_spec.spl
    1             0  02_integration/os/hosted/browser_profile_store_spec.spl
    1             0  02_integration/os/hosted/hosted_web_content_session_spec.spl
    1             0  02_integration/rendering/browser_session_event_retention_spec.spl
    1             0  02_integration/rendering/browser_session_script_css_animation_spec.spl
    1             0  02_integration/rendering/browser_session_textarea_lifecycle_spec.spl
    1             0  02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl
    1             0  02_integration/rendering/metal_msl_pipeline_spec.spl
    1             0  02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl
    1             0  02_integration/rendering/simple_web_layout_child_index_spec.spl
    1             0  02_integration/rendering/vulkan_engineNd_batch_descriptor_reuse_live_spec.spl
    1             0  02_integration/rendering/vulkan_engineNd_batch_fallback_live_spec.spl
    1             0  02_integration/rendering/vulkan_engineNd_batch_live_spec.spl
    1             0  02_integration/watcher/watcher_backend_validation_spec.spl
    1             0  02_integration/watcher/watcher_shb_integration_spec.spl
    1             0  02_integration/watcher/watcher_smf_integration_spec.spl
   25             0  03_system/acceptance/acceptanceNsystem_spec.spl
    1             0  03_system/app/browser_engine_in_qemu_spec.spl
    1             0  03_system/app/browser_in_qemu_pixel_spec.spl
    1             0  03_system/app/simple_browser_in_qemu_spec.spl
    1             0  03_system/app/browser/feature/animation_revision_hot_path_spec.spl
    1             0  03_system/app/browser/feature/browser_address_selection_backspace_spec.spl
    1             0  03_system/app/browser/feature/browser_address_url_reference_spec.spl
    1             0  03_system/app/browser/feature/browser_associated_form_controls_spec.spl
    1             0  03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl
    1             0  03_system/app/browser/feature/browser_checkable_control_rendering_spec.spl
    1             0  03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl
    1             0  03_system/app/browser/feature/browser_cookie_name_token_spec.spl
    1             0  03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.spl
    1             0  03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl
    1             0  03_system/app/browser/feature/browser_eval_error_side_effects_spec.spl
    1             0  03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.spl
    1             0  03_system/app/browser/feature/browser_home_pending_address_spec.spl
    1             0  03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.spl
    1             0  03_system/app/browser/feature/browser_hosted_hsts_transport_boundary_spec.spl
    1             0  03_system/app/browser/feature/browser_httpsNhead_redirect_spec.spl
    1             0  03_system/app/browser/feature/browser_input_event_payload_spec.spl
    1             0  03_system/app/browser/feature/browser_live_default_action_spec.spl
    1             0  03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.spl
    1             0  03_system/app/browser/feature/browser_script_history_traversal_spec.spl
    1             0  03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl
    1             0  03_system/app/browser/feature/browser_space_modifier_activation_order_spec.spl
    1             0  03_system/app/browser/feature/browser_stop_partial_focus_spec.spl
    1             0  03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl
    1             0  03_system/app/browser/feature/request_animation_frame_alignment_spec.spl
    1             0  03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl
    1             0  03_system/app/optimize/feature/pure_simple_executable_layout_spec.spl
    1             0  03_system/app/os/feature/xNNdesktop_driver_completion_spec.spl
    1             0  03_system/check/chrome_simple_web_layout_proof_validator_spec.spl
    1             0  03_system/check/electron_generated_gui_web_proof_validator_spec.spl
    1             0  03_system/check/electron_live_smoke_proof_validator_spec.spl
    1             0  03_system/check/electron_mdi_proof_validator_spec.spl
    1             0  03_system/check/electron_simple_web_engineNd_proof_validator_spec.spl
    1             0  03_system/check/electron_simple_web_layout_proof_validator_spec.spl
    1             0  03_system/check/gui_webNd_completion_criteria_placeholder_audit_spec.spl
    1             0  03_system/check/html_css_full_rendering_goal_status_spec.spl
    1             0  03_system/check/macos_vulkanNd_live_evidence_contract_spec.spl
    1             0  03_system/check/macos_vulkan_gui_widget_live_evidence_contract_spec.spl
    1             0  03_system/check/macos_vulkan_web_live_evidence_contract_spec.spl
    1             0  03_system/check/renderdoc_capture_replay_inspection_spec.spl
    1             0  03_system/check/shared_wm_renderer_unification_simple_bin_spec.spl
    1             0  03_system/check/tauri_android_render_log_validator_spec.spl
    1             0  03_system/check/tauri_ios_render_log_validator_spec.spl
    1             0  03_system/check/tauri_mobile_mdi_proof_validator_spec.spl
    1             0  03_system/check/tauri_simple_web_layout_proof_validator_spec.spl
    1             0  03_system/check/widget_shells_crossengine_spec.spl
    1             0  03_system/check/wm_browser_event_routing_validator_spec.spl
    1             0  03_system/check/wm_gui_window_drawing_spec.spl
    1             0  03_system/check/wm_multiapp_taskbar_spec.spl
    1             0  03_system/core/core_systemNspec.spl
   25             0  03_system/core/compatibility/compatibilityNsystem_spec.spl
   50             0  03_system/core/edge_case/edge_caseNsystem_spec.spl
  100             0  03_system/core/error_path/error_pathNsystem_spec.spl
   25             0  03_system/core/exploratory/exploratoryNsystem_spec.spl
   25             0  03_system/core/regression/regressionNsystem_spec.spl
   25             0  03_system/e2e/eNeNsystem_spec.spl
   25             0  03_system/e2e/functional/functionalNsystem_spec.spl
   25             0  03_system/e2e/integration/integrationNsystem_spec.spl
    1             0  03_system/feature/app/easy_fix_spec.spl
    2             0  03_system/feature/baremetal/armNboot_spec.spl
    1             0  03_system/feature/baremetal/boot_test_spec.spl
    1             0  03_system/feature/baremetal/collections_qemu_spec.spl
    1             0  03_system/feature/baremetal/compressed_logging_spec.spl
    1             0  03_system/feature/baremetal/ghdl_riscvNsemihost_spec.spl
    1             0  03_system/feature/baremetal/hello_riscvNsemihost_spec.spl
    1             0  03_system/feature/baremetal/inline_asm_integration_spec.spl
    1             0  03_system/feature/baremetal/interrupt_spec.spl
    1             0  03_system/feature/baremetal/riscvNboot_spec.spl
    1             0  03_system/feature/baremetal/scheduler_qemu_spec.spl
    1             0  03_system/feature/baremetal/startup_spec.spl
    1             0  03_system/feature/baremetal/syscall_spec.spl
    1             0  03_system/feature/baremetal/xNNboot_spec.spl
    1             0  03_system/feature/baremetal/xNboot_spec.spl
   80             0  03_system/feature/final_push/final_pushNsystem_spec.spl
    1             0  03_system/feature/platform/cross_platform_spec.spl
    1             0  03_system/feature/usage/actors_spec.spl
    1             0  03_system/feature/usage/assert_spec.spl
    1             0  03_system/feature/usage/async_effects_spec.spl
    1             0  03_system/feature/usage/future_body_execution_spec.spl
    1             0  03_system/feature/usage/futures_promises_spec.spl
    1             0  03_system/feature/usage/matNspec.spl
    1             0  03_system/feature/usage/multicore_green_agent_plan_spec.spl
    1             0  03_system/feature/usage/resource_cleanup_spec.spl
    1             0  03_system/feature/usage/table_spec.spl
    1             0  03_system/feature/usage/types_spec.spl
    1             0  03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/at_supports_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/background_gradient_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/box_shadow_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/display_invalid_cascade_spec.spl
    1             0  03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.spl
    1             0  03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl
    1             0  03_system/feature/web_platform/css/flex_rtl_main_axis_spec.spl
    1             0  03_system/feature/web_platform/css/glass_feature_gap_spec.spl
    1             0  03_system/feature/web_platform/css/grid_auto_item_stretch_spec.spl
    1             0  03_system/feature/web_platform/css/grid_foundation_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/inline_block_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/logical_sizing_writing_mode_spec.spl
    1             0  03_system/feature/web_platform/css/object_fit_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/outline_zero_cascade_spec.spl
    1             0  03_system/feature/web_platform/css/padding_shorthand_cascade_spec.spl
    1             0  03_system/feature/web_platform/css/pseudo_text_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/scrollbar_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/sticky_wpt_spec.spl
    1             0  03_system/feature/web_platform/css/table_formatting_spec.spl
    1             0  03_system/feature/web_platform/html/address_element_rendering_spec.spl
    1             0  03_system/feature/web_platform/html/code_element_rendering_spec.spl
    1             0  03_system/feature/web_platform/html/definition_list_rendering_spec.spl
    1             0  03_system/feature/web_platform/html/details_summary_rendering_spec.spl
    1             0  03_system/feature/web_platform/html/fieldset_legend_rendering_spec.spl
    1             0  03_system/feature/web_platform/html/hr_element_wpt_spec.spl
    1             0  03_system/feature/web_platform/html/html_numeric_character_references_spec.spl
    1             0  03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl
    1             0  03_system/gui/container_detect_spec.spl
    1             0  03_system/gui/cpu_simd_engineNd_diagram_evidence_spec.spl
    1             0  03_system/gui/editor_controller_spec.spl
    1             0  03_system/gui/editor_gui_spec.spl
    1             0  03_system/gui/editor_markdown_spec.spl
    1             0  03_system/gui/editor_md_language_spec.spl
    1             0  03_system/gui/editor_md_wiki_index_spec.spl
    1             0  03_system/gui/event_processing_spec.spl
    1             0  03_system/gui/headless_rendering_spec.spl
    1             0  03_system/gui/layered_simple_gui_web_engineNd_bitmap_evidence_spec.spl
    1             0  03_system/gui/linux_hosted_wm_live_window_spec.spl
    1             0  03_system/gui/linux_smf_dynlib_eNe_gate_system_spec.spl
    1             0  03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl
    1             0  03_system/gui/qemu_gtk_wm_capture_evidence_spec.spl
    1             0  03_system/gui/sdn_parsing_spec.spl
    1             0  03_system/gui/simple_web_browser_production_hardening_spec.spl
    1             0  03_system/gui/simpleos_hardening_evidence_matrix_spec.spl
    1             0  03_system/gui/tauri_chrome_surface_manifest_gate_spec.spl
    1             0  03_system/gui/tui_screen_spec.spl
    1             0  03_system/gui/unified_app_spec.spl
    1             0  03_system/gui/web_api_json_spec.spl
    1             0  03_system/gui/web_api_spec.spl
    1             0  03_system/gui/web_showcase_full_gpu_offload_spec.spl
    1             0  03_system/gui/widget_rendering_spec.spl
    1             0  03_system/gui/feature/gui_font_event_surface_spec.spl
    1             0  03_system/gui/wm_compare/.simple_resultNwm_chrome_theme_spec.spl
    1             0  03_system/gui/wm_compare/famous_site_corpus_spec.spl
    1             0  03_system/infrastructure/doc_coverage_system_spec.spl
  500             0  03_system/infrastructure/batch/batchNtestNsystem_spec.spl
   25             0  03_system/infrastructure/sanity/sanityNsystem_spec.spl
   25             0  03_system/infrastructure/smoke/smokeNsystem_spec.spl
    1             0  03_system/os/boot_smoke_spec.spl
    1             0  03_system/os/qemu/os/appscan/arm_smf_appscan_qemu_spec.spl
    1             0  03_system/os/qemu/os/appscan/riscv_smf_appscan_qemu_spec.spl
    1             0  03_system/os/qemu/os/appscan/xNsmf_appscan_qemu_spec.spl
    1             0  03_system/os/qemu/os/boot/armNboot_qemu_spec.spl
    1             0  03_system/os/qemu/os/boot/boot_smoke_qemu_spec.spl
    2             0  03_system/os/qemu/os/boot/riscvNboot_qemu_spec.spl
    1             0  03_system/os/qemu/os/boot/xNNboot_qemu_spec.spl
    1             0  03_system/os/qemu/os/cross/full_consistency_qemu_spec.spl
    1             0  03_system/os/qemu/os/interrupts/armNgic_qemu_spec.spl
    1             0  03_system/os/qemu/os/interrupts/riscv_plic_qemu_spec.spl
    1             0  03_system/os/qemu/os/interrupts/software_int_qemu_spec.spl
    1             0  03_system/os/qemu/os/interrupts/timer_qemu_spec.spl
    1             0  03_system/os/qemu/os/interrupts/xNNidt_qemu_spec.spl
    1             0  03_system/os/qemu/os/io/serial_input_qemu_spec.spl
    1             0  03_system/os/qemu/os/io/serial_output_qemu_spec.spl
    1             0  03_system/os/qemu/os/ipc/ipc_cross_qemu_spec.spl
    1             0  03_system/os/qemu/os/ipc/ipc_message_qemu_spec.spl
    1             0  03_system/os/qemu/os/ipc/ipc_port_qemu_spec.spl
    1             0  03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl
    1             0  03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl
    1             0  03_system/os/qemu/os/scheduler/priority_qemu_spec.spl
    1             0  03_system/os/qemu/os/scheduler/scheduler_cross_qemu_spec.spl
    1             0  03_system/os/qemu/os/scheduler/task_create_qemu_spec.spl
    1             0  03_system/os/qemu/os/stress/combined_stress_qemu_spec.spl
    1             0  03_system/os/qemu/os/stress/ipc_flood_qemu_spec.spl
    1             0  03_system/os/qemu/os/stress/task_storm_qemu_spec.spl
    1             0  03_system/os/qemu/os/usermode/rvNuser_exec_qemu_spec.spl
    1             0  03_system/os/wm/simpleos_wm_fullscreen_spec.spl
    1             0  03_system/quality/code_quality/os_harden_audit_spec.spl
    1             0  03_system/quality/duplicate_check/duplicate_check_regression_system_spec.spl
   25             0  03_system/quality/performance/performanceNsystem_spec.spl
   50             0  03_system/stdlib/stdlib_comprehensiveNsystem_spec.spl
   24             0  03_system/stress/stressNsystem_spec.spl
    1             0  03_system/tools/dap/dap_breakpoint_system_spec.spl
    1             0  03_system/tools/dap/dap_stack_trace_system_spec.spl
    1             0  03_system/tools/dap/dap_stepping_system_spec.spl
    1             0  03_system/tools/dap/dap_variables_system_spec.spl
    1             0  03_system/tools/jupyter/jupyter_error_system_spec.spl
    1             0  03_system/tools/jupyter/jupyter_execution_system_spec.spl
    1             0  03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl
    1             0  03_system/tools/jupyter/jupyter_notebook_server_system_spec.spl
    1             0  03_system/tools/jupyter/jupyter_state_system_spec.spl
    1             0  03_system/tools/lint/app_lint_spec.spl
    1             0  03_system/tools/lint/lib_lint_spec.spl
    1             0  03_system/tools/llm/llm_caret_live_comprehensive_spec.spl
    1             0  03_system/tools/llm/llm_caret_live_spec.spl
    1             0  03_system/tools/lsp/app_lsp_spec.spl
    1             0  03_system/tools/lsp/lib_async_lsp_spec.spl
    1             0  03_system/tools/lsp/lib_common_lsp_spec.spl
    1             0  03_system/tools/lsp/lsp_diagnostics_enhanced_spec.spl
    1             0  03_system/tools/lsp/lsp_mcp_format_spec.spl
    1             0  03_system/tools/repl/repl_basic_eval_system_spec.spl
    1             0  03_system/tools/repl/repl_commands_system_spec.spl
    1             0  03_system/tools/repl/repl_error_recovery_system_spec.spl
    1             0  03_system/tools/repl/repl_multiline_system_spec.spl
    1             0  03_system/tools/repl/repl_state_persistence_system_spec.spl
    1             0  03_system/wm/wm_full_stack_demo_spec.spl
    1             0  05_perf/cli_dispatch_perf_spec.spl
    1             0  05_perf/duplicate_check_benchmark_spec.spl
    1             0  05_perf/ipc_lNlogic_perf_spec.spl
    1             0  05_perf/lazy_parse_perf_spec.spl
    1             0  05_perf/mcp_json_perf_spec.spl
    1             0  05_perf/rust_vs_simple_comparison_spec.spl
    1             0  05_perf/smux_perf_spec.spl
    1             0  05_perf/std_benchmark_spec.spl
    1             0  05_perf/test_runner_benchmark_spec.spl
    1             0  05_perf/browser/hosted_browser_revision_wire_perf_spec.spl
    1             0  05_perf/browser/hosted_compositor_revision_cache_perf_spec.spl
    1             0  05_perf/stress/compilation_stress_large_spec.spl
    1             0  05_perf/stress/compilation_stress_medium_spec.spl
    1             0  05_perf/stress/compilation_stress_small_spec.spl
    1             0  05_perf/stress/concurrent_stress_large_spec.spl
    1             0  05_perf/stress/concurrent_stress_medium_spec.spl
    1             0  05_perf/stress/concurrent_stress_small_spec.spl
    1             0  05_perf/stress/cpu_stress_large_spec.spl
    1             0  05_perf/stress/cpu_stress_medium_spec.spl
    1             0  05_perf/stress/cpu_stress_small_spec.spl
    1             0  05_perf/stress/deep_nesting_large_spec.spl
    1             0  05_perf/stress/deep_nesting_medium_spec.spl
    1             0  05_perf/stress/deep_nesting_small_spec.spl
    1             0  05_perf/stress/file_stress_large_spec.spl
    1             0  05_perf/stress/file_stress_medium_spec.spl
    1             0  05_perf/stress/file_stress_small_spec.spl
    1             0  05_perf/stress/large_array_large_spec.spl
    1             0  05_perf/stress/large_array_medium_spec.spl
    1             0  05_perf/stress/large_array_small_spec.spl
    1             0  05_perf/stress/large_dict_large_spec.spl
    1             0  05_perf/stress/large_dict_medium_spec.spl
    1             0  05_perf/stress/large_dict_small_spec.spl
    1             0  05_perf/stress/large_string_large_spec.spl
    1             0  05_perf/stress/large_string_medium_spec.spl
    1             0  05_perf/stress/large_string_small_spec.spl
    1             0  05_perf/stress/many_iterations_large_spec.spl
    1             0  05_perf/stress/many_iterations_medium_spec.spl
    1             0  05_perf/stress/many_iterations_small_spec.spl
    1             0  05_perf/stress/multicore_green_fanout_spec.spl
    1             0  05_perf/stress/recursive_depth_large_spec.spl
    1             0  05_perf/stress/recursive_depth_medium_spec.spl
    1             0  05_perf/stress/recursive_depth_small_spec.spl
    1             0  05_perf/ui_access/ui_access_hot_paths_spec.spl
    1             0  05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl
    1             0  05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl
    1             0  feature/platform/cross_platform_spec.spl
    1             0  feature/usage/actors_spec.spl
    1             0  feature/usage/assert_spec.spl
    1             0  feature/usage/async_effects_spec.spl
    1             0  feature/usage/future_body_execution_spec.spl
    1             0  feature/usage/futures_promises_spec.spl
    1             0  feature/usage/matNspec.spl
    1             0  feature/usage/resource_cleanup_spec.spl
    1             0  feature/usage/table_spec.spl
    1             0  feature/usage/types_spec.spl
    1             0  feature/web_platform/css/pseudo_text_wpt_spec.spl
    1             0  feature/web_platform/css/selector_color_subset_spec.spl
    1             0  perf/cli_dispatch_perf_spec.spl
    1             0  perf/ipc_lNlogic_perf_spec.spl
    1             0  perf/rust_vs_simple_comparison_spec.spl
    1             0  perf/smux_perf_spec.spl
    1             0  perf/std_benchmark_spec.spl
    1             0  perf/test_runner_benchmark_spec.spl
    1             0  perf/ui_access/ui_access_hot_paths_spec.spl
    1             0  system/browser_engine_in_qemu_spec.spl
    1             0  system/browser_in_qemu_pixel_spec.spl
    1             0  system/editor_controller_spec.spl
    1             0  system/editor_gui_spec.spl
    1             0  system/editor_markdown_spec.spl
    1             0  system/editor_md_language_spec.spl
    1             0  system/editor_md_wiki_index_spec.spl
   24             0  system/stressNsystem_spec.spl
  500             0  system/batch/batchNtestNsystem_spec.spl
   25             0  system/compatibility/compatibilityNsystem_spec.spl
    1             0  system/dap/dap_breakpoint_system_spec.spl
    1             0  system/dap/dap_stack_trace_system_spec.spl
    1             0  system/dap/dap_stepping_system_spec.spl
    1             0  system/dap/dap_variables_system_spec.spl
    1             0  system/duplicate_check/duplicate_check_regression_system_spec.spl
   50             0  system/edge_case/edge_caseNsystem_spec.spl
  100             0  system/error_path/error_pathNsystem_spec.spl
   25             0  system/exploratory/exploratoryNsystem_spec.spl
   80             0  system/final_push/final_pushNsystem_spec.spl
   25             0  system/functional/functionalNsystem_spec.spl
   25             0  system/integration/integrationNsystem_spec.spl
    1             0  system/jupyter/jupyter_error_system_spec.spl
    1             0  system/jupyter/jupyter_execution_system_spec.spl
    1             0  system/jupyter/jupyter_kernel_install_system_spec.spl
    1             0  system/jupyter/jupyter_notebook_server_system_spec.spl
    1             0  system/jupyter/jupyter_state_system_spec.spl
    1             0  system/lint/app_lint_spec.spl
    1             0  system/lint/lib_lint_spec.spl
    1             0  system/llm/llm_caret_live_comprehensive_spec.spl
    1             0  system/llm/llm_caret_live_spec.spl
    1             0  system/lsp/app_lsp_spec.spl
    1             0  system/lsp/lib_async_lsp_spec.spl
    1             0  system/lsp/lib_common_lsp_spec.spl
    1             0  system/lsp/lsp_diagnostics_enhanced_spec.spl
    1             0  system/lsp/lsp_mcp_format_spec.spl
   25             0  system/performance/performanceNsystem_spec.spl
    1             0  system/qemu/os/appscan/arm_smf_appscan_qemu_spec.spl
    1             0  system/qemu/os/appscan/riscv_smf_appscan_qemu_spec.spl
    1             0  system/qemu/os/appscan/xNsmf_appscan_qemu_spec.spl
    1             0  system/qemu/os/boot/armNboot_qemu_spec.spl
    1             0  system/qemu/os/boot/boot_smoke_qemu_spec.spl
    2             0  system/qemu/os/boot/riscvNboot_qemu_spec.spl
    1             0  system/qemu/os/boot/xNNboot_qemu_spec.spl
    1             0  system/qemu/os/cross/full_consistency_qemu_spec.spl
    1             0  system/qemu/os/interrupts/armNgic_qemu_spec.spl
    1             0  system/qemu/os/interrupts/riscv_plic_qemu_spec.spl
    1             0  system/qemu/os/interrupts/software_int_qemu_spec.spl
    1             0  system/qemu/os/interrupts/timer_qemu_spec.spl
    1             0  system/qemu/os/interrupts/xNNidt_qemu_spec.spl
    1             0  system/qemu/os/io/serial_input_qemu_spec.spl
    1             0  system/qemu/os/io/serial_output_qemu_spec.spl
    1             0  system/qemu/os/ipc/ipc_cross_qemu_spec.spl
    1             0  system/qemu/os/ipc/ipc_message_qemu_spec.spl
    1             0  system/qemu/os/ipc/ipc_port_qemu_spec.spl
    1             0  system/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl
    1             0  system/qemu/os/scheduler/context_switch_qemu_spec.spl
    1             0  system/qemu/os/scheduler/priority_qemu_spec.spl
    1             0  system/qemu/os/scheduler/scheduler_cross_qemu_spec.spl
    1             0  system/qemu/os/scheduler/task_create_qemu_spec.spl
    1             0  system/qemu/os/stress/combined_stress_qemu_spec.spl
    1             0  system/qemu/os/stress/ipc_flood_qemu_spec.spl
    1             0  system/qemu/os/stress/task_storm_qemu_spec.spl
    1             0  system/qemu/os/usermode/rvNuser_exec_qemu_spec.spl
   25             0  system/regression/regressionNsystem_spec.spl
    1             0  system/repl/repl_basic_eval_system_spec.spl
    1             0  system/repl/repl_commands_system_spec.spl
    1             0  system/repl/repl_error_recovery_system_spec.spl
    1             0  system/repl/repl_multiline_system_spec.spl
    1             0  system/repl/repl_state_persistence_system_spec.spl
   25             0  system/sanity/sanityNsystem_spec.spl
   25             0  system/smoke/smokeNsystem_spec.spl
```
