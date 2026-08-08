# Test-only functions: a vacuity family nobody had enumerated (2026-08-04)

**Status:** OPEN (census landed; individual class-(ii) items to be filed/fixed per lane)

A function whose *only* callers are tests is a function a green suite proves nothing
about. Two independent instances surfaced in one investigation
(`should_keep_selective_export`, `eval_get_warnings`), which is enough to suspect a
family. This document is the enumeration.

## Method

Owned code only (`src/compiler_rust/**` minus `vendor/**`; `src/**/*.spl` minus
vendored runtime sources).

1. **Attribute references to the right `#[cfg(test)]` block.** Comments, string and
   raw-string literals are blanked first so brace counting is exact; every
   `#[cfg(...test...)]` attribute is resolved to the *item* it annotates and that
   item's brace-matched span becomes a test region. "Appears after the first
   `mod tests`" is not good enough — the seed finding depended on knowing the test
   module starts at line 1109, not merely that references sit at 1114 and 1670+.
   Whole-file test regions: any path component `tests/`, `benches/`, `examples/`.
2. **Definitions:** one production `fn` definition tree-wide, and no same-named
   definition inside a test region. Any name defined more than once anywhere is
   dropped as ambiguous — this is what keeps generic names (`new`, `len`, `parse`,
   `read`) out of the census entirely, and it also drops every trait method (the
   trait declaration plus its impl are two definitions).
3. **References:** every word-boundary occurrence outside the definition site,
   bucketed test/production by region membership.
4. **Survivors** = exactly one production definition, ≥1 test reference, 0
   production references.

## False positives, resolved

| Stage | Count |
|---|---|
| Raw `TEST_ONLY` + `REEXPORT_ONLY` candidates | 366 |
| — dropped: `#[no_mangle]` / `extern "C"` (called from C/Simple, not Rust) | 1 |
| — dropped: trait-impl methods (dispatched via the trait, not by name) | 17 |
| — dropped: referenced from owned non-Rust code (`.spl` ports, `.c`, build config) | 152 |
| **Survivors** | **197** |

Mechanical false-positive rate at this stage: **169/366 = 46.2%** — consistent with
this repo's history (a "30 drifted trait pairs" census collapsed to 0 real; a
spec-import census invented 1,105 phantom sites). Directory symlinks
(`src/app/t32_cli`) are followed with realpath de-duplication, so the 39%-of-`.spl`
blind spot does not apply.

The 152 non-Rust-reference drops are real drops, not noise. Example:
`validate_suspension_context` is test-only *within Rust*, but
`src/compiler/30.types/type_system/effects.spl` carries the pure-Simple port that
superseded it — a Rust-only census would have reported it as an unwired feature.
Markdown and `.sdn` were deliberately excluded from the reference corpus: a doc
mentioning a symbol is not a caller.

### Residual false positives: independently checked, none found

An independent validator re-derived every survivor's references with a
`#[cfg(test)]`-*unaware* rule — a reference is acceptable only if its enclosing
`fn` carries `#[test]`/`#[bench]`, or the file lives under `tests/`. 181/197 passed
outright. All 16 flagged cases were hand-inspected and every one confirmed the
census:

- `set_lint_config` @ `pipeline/mod.rs:331` — inside `#[cfg(test)]` (line 42); the
  doc comment literally reads "Test helper for running source with a specific lint
  configuration".
- `is_line_executed` @ `coverage.rs:426` — inside `#[cfg(test)]` (line 374), in a
  `was_line_executed_compat` shim. This is the documented SHIM-VACUITY pattern.
- `declare_uniform_i64_import` @ `helpers.rs:442` and `join_actor` @
  `concurrency/mod.rs:107` — **comment text**, which the census strips and the
  validator's grep does not.
- `add_source_with_semantic_dependencies` @ `incremental_builder.rs:423` — inside
  `#[cfg(test)]` (line 182).

**Residual hand-verified false-positive rate on the 197 survivors: 0/16 sampled.**

### Known false negatives — 197 is a floor, not a total

The rules that keep the false-positive rate at zero cost recall, and it is worth
being explicit about where:

1. **Ambiguous names are dropped wholesale.** Any name with more than one definition
   anywhere is excluded, which removes every trait method and every common name. It
   also removed `FunctionDef::is_test`, a genuine member of the family, because
   `let is_test = ...` is a local variable in two unrelated files (section 4).
2. **Trait-impl methods are dropped** (17 of them) because a name-based census cannot
   see dynamic dispatch. Some of those are certainly test-only in practice.
3. **A reference from anywhere in owned non-Rust code counts as production** (152
   drops). That is right for `.spl` ports and C callers, but a `.spl` file that only
   *mentions* the symbol in a string would also suppress a real finding.
4. **`NEVER_REFERENCED` is a separate, larger family** and is not counted here: 9,135
   owned Rust function names have zero references anywhere, including tests.

A recall-oriented second pass would relax rule 1 by resolving `.method()` call syntax
rather than bare words. That is the natural follow-up lane.

## Ground-truth validation

The census was run before any of its output was believed, and rediscovered both
known instances independently:

- `should_keep_selective_export` → `TEST_ONLY`,
  `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:358`,
  **9 test references, 0 production references** — matching the known "nine unit
  tests are green on a function that has never run".
- `eval_get_warnings` → `src/compiler/10.frontend/core/interpreter/eval.spl:208`,
  exported at :953 and re-exported from `interpreter/__init__.spl:15`, with **zero**
  live consumers anywhere in `src/` or `test/`.

The `.spl` arm turned out to be worse than "test-only", and the reason is a fourth
vacuity shape worth naming on its own.

## Bonus finding: `it "skipped"` specs whose assertions are commented out

`eval_get_warnings` has no test callers either — every occurrence of it under
`test/` is inside a **comment**. The four specs involved:

| spec | lines | comment lines | live asserts | commented-out asserts |
|---|---|---|---|---|
| `test/unit/compiler_core/must_use_spec.spl` | 157 | 152 | 1 | 23 |
| `test/unit/compiler_core/ignored_return_warning_spec.spl` | 147 | 142 | 1 | 28 |
| `test/unit/compiler_core/exhaustiveness_spec.spl` | 120 | 115 | 1 | 12 |
| `test/unit/compiler_core/annotation_intrinsics_spec.spl` | 93 | 88 | 1 | 11 |

Each file's single live assertion is the same tautology:

```
describe "Must Use":
    it "skipped":
        expect(pending_reason.len()).to_be_greater_than(0)
```

It asserts that the skip-reason string is non-empty — it passes iff the author typed
a reason. 74 real assertions are commented out beneath it, across 517 lines of which
497 are comments. These specs report as passing.

This is why `eval_get_warnings` is unreachable: the only code that would have called
it is commented out. A test-only-function census and a commented-out-spec census meet
here — the getter is dead because its callers were disabled, and the feature it was
built to expose (must-use / ignored-return / exhaustiveness warnings surfaced as a
list) is unverifiable as a result. This shape is not counted in the 197. A first-pass sweep of `test/**` (20,170 `.spl`
files, `/usr/bin/grep`, anchored):

| measure | count |
|---|---|
| files containing `it "skipped"` | 683 |
| files containing a commented-out `expect`/`assert`/`_assert` line | 596 |
| **files containing both** | **351** |
| commented-out assertion lines, total | 15,172 |
| live assertion lines in `test/**`, total | 363,639 |

The 351 intersection is the strong set: a spec that was disabled *and* kept its real
assertions as comments. 4.2% of all assertion-shaped lines under `test/` are
commented out. These numbers are a bound, not a verdict — a commented assertion may
be genuine illustrative documentation — but the four `compiler_core` specs above were
inspected line by line and are the disabled-and-tautological shape exactly. Sizing
the rest is a separate lane.

## `test/` symlinks `src/` into itself — and it broke this census

`find test -name '*.spl'` reports 20,166 files; a symlink-following walk reports
41,485. The gap is not incidental double-counting. `test/` contains **14 directory
symlinks that point back into the production tree**:

```
test/01_unit/compiler/compiler -> ../../../src/compiler
test/unit/compiler/compiler    -> src/compiler
test/01_unit/compiler/std      -> ...
test/feature/lib/{app,compiler,lib}
test/03_system/feature/lib/{app,compiler,lib}
test/01_unit/app/desugar/app,  test/unit/app/desugar/app
test/01_unit/lib/database/lib, test/unit/lib/database/lib
```

Consequence for any census: production source files are re-reached through a `test/`
path and get classified as *tests*. Measured on this tree, a follow-links walk of
`test/` yields 41,485 `.spl` files, of which **11,392 — 27% — are production files
under `src/` reached through a symlink**. That is precisely how the `.spl` arm failed
its own ground-truth check — twice. `eval_get_warnings` was dropped by the
name-shadowing rule because its **own definition**, reached via
`test/01_unit/compiler/compiler/10.frontend/core/interpreter/eval.spl`, registered as
a test-side definition of the same name. The census was measuring `src/compiler`
against itself.

The fix is to treat the **realpath** as identity: a file whose realpath lives under
`src/` is production no matter which path reached it. Anyone writing a
src-versus-test analysis in this repo must do this, and it is the mirror image of the
already-documented `src/app/t32_cli` symlink trap — that one causes a non-following
walk to *miss* 39% of `.spl` files; this one causes a following walk to *invent* a
test tree out of production code.

This is worth a second look beyond censuses: `test/unit/compiler/compiler` being a
live symlink to `src/compiler` means a directory-mode test run over `test/` walks
into production sources.

## The `.spl` arm

With realpath identity and the export/use exclusion both in place, the pure-Simple
arm passes its ground-truth check. `eval_get_warnings` is rediscovered at
`src/compiler/10.frontend/core/interpreter/eval.spl:208` with **0 test references**
and 2 production references that are *both re-export lines*
(`interpreter/__init__.spl:15` and `eval.spl:953`) — i.e. classified
`NEVER_REFERENCED`, which is stricter than "test-only" and matches the hand-grep.

Over 13,917 `src/**.spl` files and 30,083 genuine `test/**.spl` files (41,485 walked
minus 11,392 symlink aliases), against 78,532 distinct `fn` names:

| class | count |
|---|---|
| `TEST_ONLY` — referenced only from `test/**` | 2,030 |
| `NEVER_REFERENCED` — no caller anywhere, including tests | 4,883 |

459 of the 2,030 have production references that are *only* `export`/`use` lines.

`TEST_ONLY` concentration by area:

| area | count |
|---|---|
| `src/compiler/70.backend` | 434 |
| `src/os/kernel` | 299 |
| `src/os/crypto` | 203 |
| `src/os/services` | 137 |
| `src/compiler_rust/lib` | 130 |
| `src/os/drivers` | 89 |
| `src/os/compositor` | 74 |
| `src/compiler/10.frontend` | 66 |

The `src/os/*` concentration (over 850 across kernel, crypto, services, drivers,
compositor, libc, apps) is the SimpleOS surface and is the obvious next lane —
`src/os/crypto` in particular, given this repo's history of fabricated KATs and dead
crypto entry points. These counts carry the same caveats as the Rust arm: the
one-definition-tree-wide rule suppresses ambiguous names, so 2,030 is a floor, and
individual triage into (i)/(ii)/(iii) has *not* been done for the `.spl` arm.

## Triage (Rust arm)

| Class | Count | Meaning |
|---|---|---|
| (i) dead code | 141 | unused accessors, `with_*`/`set_*` builders (32 of them), thin delegating wrappers, duplicated convenience layers |
| (ii) unwired feature | 31 | the function is correct; nothing connects it. The valuable class. |
| (iii) legitimately test-only | 25 | mock/bench/test-DB helpers and test observers — fine, no action |

The class boundary was drawn by name/doc shape (predicate, check/filter/validate/warn,
builder, accessor) and then hand-corrected. 34 landed in class (ii) by shape; three
were demoted on inspection — `warn_shared_mutation` and `warn_unique_copied` to
class (i), because the behaviour they name *is* implemented and live elsewhere (see
"Fixed in this change"), and `quarantine_contains` to class (iii), because it observes
a mechanism that does run. The 12 highest-consequence class-(ii) items were each
traced to their intended consumer by hand; the rest are recorded but not individually
traced. Every demotion is stated in the ranked list rather than dropped, so the
count can be audited against the reasoning.

Class (iii) is `compiler/src/mock.rs`, `wasm-runtime/src/browser_mock.rs`,
`runtime/src/value/bench_support.rs`, `runtime/src/value/sffi/io_capture.rs`
(`rt_has_mock_stdin`), `driver/src/test_db/runs.rs`, and
`interpreter_extern/memory.rs` (`quarantine_contains`). These are test
infrastructure by design.

## Class (ii), ranked by consequence

### 1. WASI sandbox capability enforcement is never fed — `wasm-runtime/src/wasi_env.rs`

`WasiConfig::validate_capabilities()` (:268) **is** wired into the production run
path (:355). It fails **open**:

```rust
let Some(table) = &self.capability_table else {
    return Ok(());
};
```

The only way to populate `capability_table` is `with_capability_table` (:224), whose
only callers are unit tests. The only parser that could build such a table from the
compiler's own generated manifest, `WasiCapabilityTable::from_sandbox_lowering_sdn`
(:81), is likewise called only from a unit test (:514) — even though the compiler
does emit `sandbox_lowering.sdn` (`compiler/src/security.rs:2264`,
`driver/src/cli/security.rs:254`).

**What goes unenforced:** every WASI env-var grant and every preopened directory.
The producer (compiler emits the manifest) and the consumer (runtime validates
against a table) both exist and are both tested; nothing joins them.

**Honest scope limit:** the single production construction site,
`driver/src/exec_core.rs:677`, is `WasiConfig::new()` with no env vars and no
preopen dirs, so today `validate_capabilities()` would pass vacuously even with a
table attached. The gap is therefore latent, not currently exploitable — the moment
any caller adds a grant, it is granted unchecked. Fixing it means wiring
`from_sandbox_lowering_sdn` → `with_capability_table` at that construction site,
which needs a decision about where the `.sdn` is located at run time.

### 2. Escaping-reference analysis: both halves dead — `compiler/src/hir/lifetime.rs`

`check_escape` (:432) is the general "does this reference outlive its target scope"
entry point; it pushes `LifetimeViolation::EscapingReference`. It has no production
caller. Only the return-position special case, `check_return` (:450), is reached
(recursively from :467), and its violations do surface — `pipeline/lowering.rs:172`
consumes `EscapingReference`.

**What goes unenforced:** escapes by any route other than a return — storing a
reference into a longer-lived scope, for example. `E200x` is only ever raised for
returns.

Compounding this: warning code **W1004 (escaping borrow) has no producer at all**.
Its only emitter was `MemoryWarningCollector::warn_escaping_borrow`, itself dead
(see the fix below); `memory_check.rs` emits W1001/W1002/W1003/W1005/W1006 and
never W1004.

### 3. Import-cycle detection is never invoked — `compiler/src/module_resolver/resolution.rs:975`

`check_circular_dependencies` wraps `import_graph.check_cycles()`, which is
extensively tested at the tracker level (`dependency_tracker/src/graph.rs`, 10+
assertions). The compiler-side wrapper that would apply it to a real import graph
has no production caller.

**What goes unenforced:** cyclic imports get whatever the resolver does naturally
instead of the `circular_dependency` diagnostic that was written for them.
`di.rs:1328 check_circular` (DI graph, DFS) is the same shape.

### 4. The whole `FunctionDef` decorator-introspection API is test-only — `parser/src/ast/nodes/definitions.rs`

Anchored method-call counts (`\.name()`, `/usr/bin/grep`, vendor excluded):

| method | total call sites | production call sites |
|---|---|---|
| `is_test` (:135) | 6 | **0** |
| `is_property_test` (:119) | 8 | **0** |
| `is_snapshot_test` (:127) | 6 | **0** |
| `property_test_config` (:144) | 3 | **0** |
| `snapshot_test_config` (:153) | 2 | **0** |
| `has_simd_decorator` (:111) | 3 | **0** |
| `has_effects` (:106) | 1 | **0** |
| `is_generated` (:162) | 7 | 2 (`driver/src/cli/analysis.rs:78,209`) |

**What goes unenforced:** everything the parser knows about `@test`,
`@property_test(iterations: N)`, `@snapshot_test(name:, format:)`, `@simd` and
effect annotations at the AST level. The decorators are parsed, stored, exposed
through a complete accessor API, unit-tested — and no compiler stage ever asks. Only
`@generated_by` provenance is actually consulted, by one CLI analysis command.

*Self-correction, recorded because it is the trap this repo keeps hitting:* the first
pass of this section claimed `is_test` was the live accessor that superseded the
specific ones. That was wrong. `is_test` appeared to have production references only
because `let is_test = ...` is a local variable in `driver/src/cli/test_discovery.rs`
and `util/arch_test/src/rules.rs` — a bare-name collision, which is also why the
automated census dropped `is_test` as ambiguous instead of reporting it. The census's
one-definition-tree-wide rule protects it from *false positives* at the cost of
false negatives exactly here; only the anchored `\.is_test()` recount surfaced it.

### 5. Selective-export filtering — `interpreter_module/module_loader.rs:358` (DO NOT WIRE HERE)

The seed finding, restated for completeness. `should_keep_selective_export` would
enforce `use mod.{a, b}` name lists; the real loader at :829 computes the requested
name list and then does `let mut filtered_items: Vec<Node> = module.items;`,
keeping everything. Nine unit tests are green on it.

**Deliberately left alone.** Narrowing the registered module surface changes symbol
resolution repo-wide; an in-tree comment records that a prior narrowing attempt was
reverted because entrypoints depend on unnamed private helpers; and it needs "what a
module registers to evaluate itself" separated from "what an importer may name"
first. Another lane owns this. `filter_glob_import` (:989, "implements the formal
model's `globImport` function") is the same shape in the same file and carries the
same risk — also left alone.

### 6. Lower-consequence class (ii)

`can_call_unverified` (`hir/types/verification.rs:46` — "only trusted boundaries can
call unverified code from verified context"; its siblings `is_verified`/`is_trusted`
are wired, this one is not), `statement_needs_await` (`type/src/effects.rs:343`),
`has_lint_warnings` (`pipeline/core.rs:172`), `validate_bug_record`
(`driver/src/bug_db.rs:516`), `is_actor_builtin` (`compiler/src/compilability.rs:917`),
`check_escape`'s neighbour `enter_ghost` (`hir/types/verification.rs:178`).

Two candidates were demoted out of class (ii) on inspection and are recorded here so
the demotion is not silently lost:

- `quarantine_contains` (`interpreter_extern/memory.rs:112`) reads the
  use-after-free quarantine ring. The ring itself *is* maintained in production —
  `harden_quarantine_free` is called at :649 and the ring is read at :153. This
  function is a test *observer* of a live mechanism, i.e. class (iii), not an
  unenforced gate.
- `can_start_module` (`pipeline_parallel.rs:288`) is real, but `max_in_flight` going
  unenforced is a symptom of a **wholly dead module**, not of one unwired predicate
  (see below).

## Cross-cutting: 8 survivor files are wholly dead modules

For each of the 110 files holding a survivor, the file's own `pub struct`/`pub
enum`/`pub trait` names were checked against every other owned `.rs` file. Eight
files have public types that **appear nowhere else in owned Rust**, which accounts
for 22 of the 197 survivors:

| module | public types | note |
|---|---|---|
| `compiler/src/pattern_analysis.rs` | `ExhaustivenessCheck`, `PatternAnalysis` | match-exhaustiveness analysis |
| `compiler/src/effects_cache.rs` | `EffectCache`, `EffectCacheConfig`, `EffectCacheStats` | 8 survivors live here |
| `compiler/src/pipeline_parallel.rs` | `ParallelPipeline`, `PipelineConfig`, `PipelineCoordinator` | the `max_in_flight` case |
| `compiler/src/codegen/wasm_bindgen_gen.rs` | `BindgenCodeGenerator`, `BindingExtractor`, `BrowserBinding` | |
| `simd/src/intrinsics.rs` | `SimdIntrinsics`, `CraneliftSimdType`, `SimdInstruction` | |
| `runtime/src/value/primitive_sort.rs` | `PrimitiveSortDispatch`, `PrimitiveSortKind` | the specialized sort path |
| `gpu/src/optimize.rs` | `AccessPattern`, `BankConflict` | |
| `compiler/src/mock.rs` | `MockBehavior`, `MockConfig` | expected — test infrastructure |

`pattern_analysis.rs` is worth singling out: `ExhaustivenessCheck` is a dead module,
and `test/unit/compiler_core/exhaustiveness_spec.spl` is one of the four
`it "skipped"` specs described below. The analysis and its spec were disabled
independently and neither disablement is visible from a green suite.

This points at an adjacent, larger family: **9,135 owned Rust function names have
zero references anywhere in the tree, including tests.** That is out of scope here
and is not the same finding — a never-referenced function is honestly dead, whereas
a test-only function is dead code wearing a green badge.

## Fixed in this change

`compiler/src/hir/lower/memory_warning.rs` — deleted a six-function dead
convenience layer: `warn_shared_mutation`, `warn_unique_copied`,
`warn_mutable_shared`, `warn_escaping_borrow`, `warn_potential_cycle`,
`warn_missing_mut`. Five unit-test call sites kept two of them looking alive.

This is class (i), not class (ii), and the evidence for that is textual: the live
emitter `memory_check.rs` builds the same warning codes **inline** with *richer*
context strings, and the dead wrappers had drifted to truncated ones —

| code | live text (`memory_check.rs`) | dead wrapper text |
|---|---|---|
| W1001 | shared pointers (\*T) are read-only; use COW pattern | shared pointers (\*T) are read-only in strict mode |
| W1002 | unique pointers (&T) are move-only; use explicit `move` or `.clone()` | unique pointers (&T) are move-only |
| W1003 | shared pointers cannot be reassigned; use `val` instead of `var` | shared pointers cannot be reassigned |

So wiring them would have **regressed** diagnostic quality. Deletion is the correct
action, per the project rule that unused code is deleted completely and a test
guarding deleted code goes with it. The two collector tests were kept — they cover
`count()`, `has_warnings()` and `summary()`, which are real — and rewritten to
construct warnings exactly the way production does.

### Evidence

`cargo check -p simple-compiler --lib --tests` after deleting all six wrappers:
`Finished dev profile ... in 1m 31s`, **0 errors**. Nothing outside the test module
referenced them; an anchored recount over `src/compiler_rust/**` (vendor excluded)
returns **0** occurrences of any of the six names.

Baseline, after the rewrite:

```
test hir::lower::memory_warning::tests::test_collector_basic ... ok
test hir::lower::memory_warning::tests::test_collector_summary ... ok
test hir::lower::memory_warning::tests::test_strict_mode ... ok
test hir::lower::memory_warning::tests::test_warning_codes ... ok
test hir::lower::memory_warning::tests::test_warning_format ... ok
test hir::lower::tests::lifetime_tests::test_memory_warnings_no_false_positives ... ok
test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 3598 filtered out
```

**Sabotage** — `MemoryWarningCollector::warn` changed to drop the warning instead of
pushing it (`let _ = warning;`). Exactly the two rewritten tests fail, and they fail
on the value they assert, not on a compile error:

```
test hir::lower::memory_warning::tests::test_collector_summary ... FAILED
test hir::lower::memory_warning::tests::test_collector_basic ... FAILED

---- test_collector_basic stdout ----
panicked at compiler/src/hir/lower/memory_warning.rs:344:9:
assertion `left == right` failed
  left: 0
 right: 2

---- test_collector_summary stdout ----
panicked at compiler/src/hir/lower/memory_warning.rs:365:9:
assertion `left == right` failed
  left: 0
 right: 3

test result: FAILED. 4 passed; 2 failed; 0 ignored; 0 measured; 3598 filtered out
```

`left: 0` against `right: 2` and `right: 3` are the collected-warning counts the
rewritten tests assert — the rewrite still observes real collector behaviour and is
not vacuous. Sabotage reverted; suite back to `6 passed; 0 failed`.
