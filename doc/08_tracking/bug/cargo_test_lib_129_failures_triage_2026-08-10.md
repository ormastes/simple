# `cargo test -p simple-compiler --lib` — 135-failure triage (2026-08-10)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

### RESOLVED 2026-08-10 — poison recovery applied, 24 results un-masked

Applied `lock().unwrap_or_else(|e| e.into_inner())` to every test-serialization
`Mutex<()>` guard (these serialize env-var mutation between tests; they guard no
shared data, so recovering the inner guard after a panic is sound):

- `pipeline/native_project/tests.rs` — all `*_lock().lock().unwrap()` call sites
  for the three guards at lines 227 (`simd_tier_env_lock`), 232
  (`process_dir_lock`), 636 (`no_stub_fallback_env_lock`), plus every
  `runtime_bundle_env_lock()` site (35 lines total).
- `pipeline/execution.rs` — 10 `runtime_bundle_env_lock()` test sites (the guard
  itself is defined here as `runtime_bundle_env_lock_for_tests`, line 138).
- `interpreter_extern/gpu.rs` — 4 `TEST_LOCK` sites in `device_mem_counter_tests`.

`VK_STATE` and `DEVICE_ALLOCS` were deliberately left alone — those protect real
shared state, where poisoning is meaningful.

**Measured on this commit's parent vs. this commit** (`cargo test -p
simple-compiler --lib`, full suite both sides; the baseline had already drifted
from 129 to 78 failures because of sibling fixes landing the same day):

| | before | after |
|---|---|---|
| passed | 3,616 | 3,640 |
| failed | 78 | **54** |
| `PoisonError` occurrences | 26 | **0** |

Set-diff: **24 fixed, 0 new**. All 24 were masked results that pass once
un-masked — 22 `native_project::tests::*` (the `runtime_bundle_*` /
`stage4_*` family) and 2 `device_mem_counter_tests`
(`free_of_untracked_ptr_is_a_safe_noop`,
`live_and_peak_externs_read_the_same_atomics`). None of the un-masked tests
turned out to be a genuine failure.

The remaining genuine failures in these modules are **still visible and now
report their real messages** rather than `PoisonError` — e.g.
`device_mem_counter_tests::alloc_bumps_live_and_peak_bytes` and
`::peak_survives_free_seeded_leak` now show `assertion left == right failed` at
`gpu.rs:108`, and 15 `native_project::tests::*` (core-c lane / stage4 / import-map)
continue to fail on their own assertions. This change altered only how results
are reported; it hid nothing.

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

### RESOLVED 2026-08-10 — it was a LATENT COMPILER DEFECT, now fixed

**Verdict: the fail-open is wrong, not the tests.** Archaeology + an end-to-end
probe settle it.

*Archaeology.* `name.contains("::")` entered on 2026-02-27 (`6da00decc78`, "fix:
improve parser for native-build success (62→52 failures)") as the **error gate** —
`if name.contains("::") { return Err("unknown enum variant") }`, commented
"genuine error". Some later commit inverted it into the **success** condition
(`variant_exists || ANY || contains("::")`). Every commit that touched the
predicate since is a `chore:`/`wip:` bulk sync or a tree-wipe/restructure, so the
inversion has no reviewed rationale anywhere in history — only the in-code
"rather than failing the build" comment, written to unblock a *different* defect
(cross-module type-registry losing an enum's metadata for `Effect::Compute`).

*Downstream severity: dangerous, not harmless.* Real program, seed compiler:

    enum Color: Red / Green
    val d = Color.Nope        # or Color::Nope
    match d: case Color.Red … case Color.Green …

JIT/MIR path: **compiles clean, runs, matches no arm, exits 0.** Interpreter on
the identical file: `error: semantic: unknown variant or method 'Nope' on enum
Color`. `EnumUnit` never consults the variant list, so the fabricated value's
discriminant is a hash of the undeclared name — same silent-garbage class as the
sibling `E.no_such_name()` call-path defect.

*Narrow fix, and it already had a precedent.* `lowering_expr_call.rs:467` fixed
exactly this for the **call** path with a tri-state guard; the **ident** path was
simply missed (an unswept sibling). Applied the same guard to
`lowering_expr_ident.rs`: reject only when `enum_declares_variant(head, tail) ==
Some(false)` and the name is neither a registered global nor a lowered function.
`enum_declares_variant` returns `None` for any head that does not positively
resolve to a concrete enum, so the metadata-loss case the widening was written
for (`Effect::Compute`, enum missing from the registry) **stays permissive** — the
build it was protecting cannot regress.

*Consequence for these 51 tests.* They are legitimate; only the fixture was
stale. `Bogus::Nope` on a registry-less lowerer is indistinguishable from
metadata loss, so `helpers.rs` now registers `enum Bogus { Real }` and points
`gpu_lowerer_setup` at it — the fixture fails for the right reason and all 51
assertions are restored unweakened.

Changed: `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ident.rs`,
`.../tests/branch_coverage/helpers.rs`, `.../tests/branch_coverage/types.rs`
(two new regression tests: undeclared variant rejected for both `::` and `.`
spellings; declared variant *and* unresolved head still emit `EnumUnit`).

**Still open (separate, unfixed):** `lower_expr` remains structurally fail-open
for the other five shapes the triage probed (`Deref`, `FieldAccess` on i64,
`Await`, `Index`, `StructInit` with a bogus `TypeId`) — none of them can error.
That is a wider audit, not covered here.

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
2. ~~**Category B (51 tests)**~~ — RESOLVED 2026-08-10: it was a latent compiler
   defect (silent acceptance of undeclared enum variants). Narrow fix + fixture
   repair landed; see the Category B section above.
3. **Category D hir::lower actor/optional-struct inference (4)** — smells like
   one shared root cause in field-type inference; highest fix-per-effort ratio.
4. **Category E** — needs a toolchain/runtime owner; start with the SIGABRT,
   which is the only hard crash.

## Prevention

Same theme as the predecessor: a compile-broken test target let both a stale
production premise (B) and a bulk-edit syntax error (C) sit invisible. Gate
`cargo test -p simple-compiler --lib --no-run` in CI so the target can never
silently stop compiling again.

## Category D triage round 2 — 2026-08-10 (measured against `origin/main`)

**Re-derived baseline, not the stale 129/17.** Measured in a PINNED tree
(`git archive origin/main` @ `29cbe704e59`, private `CARGO_TARGET_DIR`) because
the shared working copy is 231 commits behind origin and carries other agents'
in-flight LLVM/codegen edits.

    cargo test -p simple-compiler --lib   ->   3,640 passed / 54 failed

Category B's 51 `gpu_errors` failures are gone, confirming that fix landed.
Three Category D items root-caused and fixed below; **54 -> 47**, set-diff
**8 genuine fixed, 0 genuine new** (two entries flip in and out across runs and
are pre-existing flakes, see the note at the end).

### D-1 FIXED — `val`/`var`-prefixed fields silently DROPPED in `struct` and `actor` bodies

`test_actor_type_visible_in_hir_scope`, `test_actor_usable_after_declaration`
both failed `CannotInferFieldType { struct_name: "Counter", field: "count",
available_fields: [] }`.

Bisected by probe. Rewriting the identical fixture with `class` instead of
`actor` lowers CLEAN, so it is not an HIR-registration bug at all:

    PROBE register_class name=Counter fields=[("count", TypeId(5))]   # class
    PROBE parse_actor    Counter fields=0 methods=0                   # actor
    PROBE register_class name=Counter fields=[]                       # actor

The actor reaches HIR with **zero fields**. Root cause is in the PARSER:
`parse_class_body` (`parser/src/types_def/mod.rs:736`) routes a `val name: Type`
line to `parse_field`, which has explicitly supported the `val`/`var` field
prefix since the StructInit header-slot fix. But `parse_indented_fields_and_methods`
(line 529 — the helper used by `parse_struct` **and** `parse_actor`, NOT by
`parse_class`) intercepted every `Val`/`Var` token first and skipped to end of
line, with the comment "Skip val/var bindings inside struct bodies … desugared
type variables: `val _tv_0 = [[text], [text]]`".

That skip is right for a type-variable BINDING and wrong for a FIELD. The
distinguishing token is the `:` right after the name. Added
`val_var_prefix_is_a_field()` (2-token lookahead via the existing `peek_nth`)
and gated the skip on it; a real field now falls through to `parse_field`.

Downstream severity note: a dropped field does not fail closed. `get_field_info`
falls back to a global "search every struct for a field with this name" heuristic
(`type_resolver.rs:602-646`), so `s.count` on a field-less struct silently
resolves to some OTHER struct's byte offset. Same silent-garbage class as the
enum-variant defect in Category B.

**Blast radius: zero on existing sources.** An indentation-aware scan of every
`.spl` under `src/` finds no `val`/`var`-prefixed field in any real `struct` or
`actor` body (the only two textual hits are inside a `tensor.spl` docstring, i.e.
lexed as a string). No existing struct layout can shift; the fix unblocks the
syntax and the two actor tests. `cargo test -p simple-parser` stays 459/459 green.

Changed: `src/compiler_rust/parser/src/types_def/mod.rs`.

### D-2 FIXED — stdlib public-API lint exemption only matched ABSOLUTE paths

`test_public_api_lints_skip_stdlib_{infra,testing,tooling}_paths` (3 tests).

`LintChecker::is_non_surface_path` (`compiler/src/lint/checker_core.rs:176-178`)
tested `path.contains("/src/compiler_rust/lib/std/src/infra/")` — with a LEADING
SLASH. Lint is routinely invoked with a repository-relative path
(`bin/simple lint src/compiler_rust/lib/std/src/infra/x.spl`), which never
matches, so the same file got `PrimitiveApi`/`BareBool` surface lints depending
on how its path was spelled. Production defect, not a test defect. Dropped the
leading `/` from the three patterns; the match stays anchored on
`src/compiler_rust/lib/std/src/…`.

Changed: `src/compiler_rust/compiler/src/lint/checker_core.rs`.

### D-3 FIXED (stale fixture) — `unnamed_duplicate_typed_args` expected line numbers off by one

`test_unnamed_duplicate_typed_args_same_file_named_rewrite_fix` (left 5, right 4),
`…_same_file_partial_named_rewrite_fix` (8 vs 7), `…_wrong_label_has_no_easy_fix`
(5 vs 4).

**The production line numbers are correct; the expectations were miscounted.**
Each fixture string starts directly with `pub fn point(...)` (no leading newline),
so the offending call site is the 5th/5th/8th line, not the 4th/4th/7th. Probed
every other assertion in the same tests and all of them already matched EXACTLY:

    named_rewrite[0] line=5 col=24 new_text="x: 3 + 1"
    named_rewrite[1] line=5 col=31 new_text="y: 4 * 2"
    partial          line=8 col=30 new_text="y: next_value()"
    wrong_label      line=5 col=27 easy_fix_none=true

A correct column on a wrong line is not possible from a diagnostic that is
genuinely off by one — the span points at the right token. `git log -L` shows the
three tests entered in a single bulk commit and the target has not compiled since,
so these three integers were never executed. Corrected the expected lines to the
verified values with an in-test note; no assertion was weakened or removed.

Changed: `src/compiler_rust/compiler/src/lint/mod.rs`.

### Measurement / flakes

Four full-suite runs in the pinned tree: 54 (base), 50, 49, 47. Three tests move
in and out of the failure set independently of any change and PASS in isolation —
`interpreter_sffi::tests::test_definition_snapshot_seeds_worker_thread`,
`watchdog::tests::test_watchdog_triggers_timeout`,
`watchdog::tests::test_watchdog_crash_log_includes_spec_context`. They are
order/timing-dependent on shared global state, are pre-existing, and should not be
attributed to any fix in this document. Excluding them the result is
**8 fixed, 0 new**.

### Still open in Category D (investigated, NOT fixed)

- `hir::lower::tests::expression_tests::{text_rfind_uses_string_method_lowering,
  uppercase_string_is_empty_uses_string_method_lowering}` and the 6 sibling
  `expression_tests` failures — these assert `HirExprKind::MethodCall` with
  `DispatchMode::Static` for string-method lowering. NOT attempted here:
  `expression_tests.rs` and the ident/field-inference lowering path they exercise
  are being edited concurrently by another agent (campaign 7c), and a fix would
  collide. Needs a separate pass once that tree settles.
- `pipeline::native_project` import-map / layout (vtable_type_owners anchoring,
  cross-module optional-struct payload type, duplicate-struct sidecar
  `UnknownType { type_name: "CompilerContext" }`) — untouched; `native_project`
  files are off-limits this session.
- Category E heavyweight archive/runtime contract tests — unchanged.

## Evidence 2026-08-17 (fleet worker A, rust-seed slice)

This doc's own concrete action item — replace the poisoning
`static LOCK: OnceLock<Mutex<()>>` guards with
`lock().unwrap_or_else(|e| e.into_inner())` so one panic stops laundering 25
unrelated results — was confirmed **still unapplied**: the raw
`OnceLock<Mutex<()>>` declarations are present at
`src/compiler_rust/compiler/src/pipeline/native_project/tests.rs:228`, `:233`,
and `:637`.

**Verdict: SKIPPED — claimed by another lane.** `pipeline/native_project/**` is
on this fleet's do-not-touch list, so this worker made no edit despite the fix
being small and well-specified. Whoever owns that path should apply it; it is
the single highest-leverage item in this triage (it unmasks 25 of 135 failures).
**Not proven:** the remaining 129 failures were not re-run (`cargo test` needs
an isolated `CARGO_TARGET_DIR` and competes with the live bootstrap).
