# `cargo test -p simple-compiler --lib` — 135-failure triage (2026-08-10)

**Status:** TRIAGED (6 fixed, 129 remain)
**Predecessor:** `cargo_test_lib_e0063_missing_struct_owner_fields_2026-08-09.md`

The E0063 fix (`0a99948d436`, confirmed ancestor of `origin/main`) made this
target compile for the first time. Baseline run: **3,557 passed / 135 failed**.
After the fix in this document: **3,563 passed / 129 failed**, with a
before/after set-diff showing 6 fixed and **0 new**.

## Category A — cascade artifacts, NOT defects (25 of 135)

29 failures reported `PoisonError`. `native_project/tests.rs` and the GPU
device-mem-counter tests share `static LOCK: OnceLock<Mutex<()>>` guards
(tests.rs:227/232/636). A test that panics while holding one poisons it, and
every later `.lock().unwrap()` fails with `PoisonError` — masking each test's
real message.

Re-ran all 29 in isolation: **25 pass** (22 of 26 `native_project`, all 3
`device_mem_counter_tests`). Only 4 are genuine (folded into Category D).

**Confidence: high** (direct isolated-run evidence both ways).
**Action:** these guards should use `lock().unwrap_or_else(|e| e.into_inner())`
so one panic stops laundering 25 unrelated results.

## Category B — assertion on a production branch that no longer exists (51)

50 `mir::lower::tests::branch_coverage::gpu_errors` + 1 `…::memory`, all
`assertion failed: result.is_err()`, all built on one helper:

    // helpers.rs:75 — "make an expression that causes lower_expr to return Err"
    HirExprKind::Global("Bogus::Nope")

`lower_global_expr` (`mir/lower/lowering_expr_ident.rs:45`) was **deliberately
widened** to `if variant_exists || expr_ty == ANY || name.contains("::")` with
an in-code comment saying it emits `EnumUnit` by name "rather than failing the
build". So the helper cannot fail any more.

I probed 6 candidate replacement expressions (`Deref`, `FieldAccess` on i64,
`Await`, `Index`, `StructInit` with a bogus `TypeId`, and the current helper):
**every one lowered OK**. `lower_expr` is now fail-open for all leaf shapes, so
the GPU-intrinsic argument-error branches these 51 tests target are
**unreachable dead code**.

**Confidence: high** (root cause read in production source + empirical probe).
**Not a mechanical fix** — it needs a decision: restore an error path, or delete
51 tests plus the dead branches. Deliberately left RED per the testing rule.
All 51 consumers of `failing_expr()` currently fail, so there is no passing
consumer to protect when this is addressed.

## Category C — FIXED: C-style comments in Simple source fixtures (6)

`lint::tests::test_allow_*` / `test_known_attribute_no_warning` failed with
`parse failed`. Real message:

    parallel operator // requires a left operand; use # for comments

**In Simple, `//` is the parallel operator; comments are `#`.** Six fixture
lines in `lint/mod.rs` (389, 404, 430, 1789, 1803, 1818) had the form
`{} // reason: …` — a `// reason:` justification bulk-inserted into Simple
source embedded in Rust string literals by a lint-reason campaign that could
not run these tests (introduced via `chore:`-labelled sync commits).

**Fix:** moved each justification onto its own line and changed `//` to `#`,
preserving the reason text. Family enumerated: `grep` confirms exactly 6
occurrences repo-wide in `src/compiler_rust/compiler/src/**.rs`; the full-log
`parallel operator //` count is now 0.

**Evidence:** `lint::tests` 12 failures → 6; full suite 135 → 129; set-diff
shows these exact 6 fixed and 0 new.

## Category D — genuine logic defects (≈17)

- `hir::lower` (11): `CannotInferFieldType` for actor types
  (`test_actor_type_visible_in_hir_scope`, `test_actor_usable_after_declaration`),
  `Unsupported("cannot infer field type")` for optional imported struct returns
  (`MouseEvent?`), and string-method lowering not producing `HirExprKind::MethodCall`
  (`text_rfind_…`, `uppercase_string_is_empty_…`).
- `native_project` import-map / layout (≈4): `vtable_type_owners` anchoring,
  cross-module optional-struct payload type, duplicate-struct sidecar
  `UnknownType { type_name: "CompilerContext" }`.
- `lint` (6 residual): `test_public_api_lints_skip_stdlib_{infra,testing,tooling}_paths`
  and 3 `test_unnamed_duplicate_typed_args_*` fix-suggestion mismatches.

**Confidence: high that these are real; root causes not investigated.**

## Category E — heavyweight archive/runtime contract tests (≈11)

`native_project` Stage-4 / core-lane tests that build, link and execute real
artifacts: `SIGABRT` in `test_core_c_runtime_native_focus_contract`,
`stage4_sqlite_probe failed: status=exit status: 2`, LSP `missing framed
response`, Mach-O `_class_addMethod`, ELF `.text` extraction, and several
"Stage4 archive core defines/retained …" contract violations.

Note: the predecessor doc guessed these were "missing `target/` artifacts".
**That is wrong** — `target/{debug,release,bootstrap}/libsimple_runtime.a` and
friends all exist in this checkout. These are real contract mismatches or
toolchain-environment issues, not absent inputs.

**Confidence: medium** on the sub-split; high that they are not "missing artifacts".

## Prioritized recommendation for a dedicated triage

1. **Category A poison guards** — one-line change, un-masks 25 results and stops
   every future run from lying about which test broke. Do this first.
2. **Category B (51 tests)** — biggest single block. Decide: is
   `lower_expr` being fail-open for unknown globals correct? If yes, delete the
   51 tests and the dead error branches. If no, that fail-open is itself a
   latent compiler defect worth its own bug.
3. **Category D hir::lower actor/optional-struct inference (4)** — smells like
   one shared root cause in field-type inference; highest fix-per-effort ratio.
4. **Category E** — needs a toolchain/runtime owner; start with the SIGABRT,
   which is the only hard crash.

## Prevention

Same theme as the predecessor: a compile-broken test target let both a stale
production premise (B) and a bulk-edit syntax error (C) sit invisible. Gate
`cargo test -p simple-compiler --lib --no-run` in CI so the target can never
silently stop compiling again.
