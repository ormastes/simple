# `parse_full_frontend` crashes on some single-item `use MODULE.{name}` imports

**Status:** RESOLVED (2026-07-29, lane IMP1) — root cause was NOT in the
frontend; see "Actual root cause" below. No `src/compiler/10.frontend/**`
change was needed or made.
**Found:** 2026-07-29 (lane RIS1, `resolve_import_symbols_spec.spl` repair)
**Area:** ~~frontend parsing/desugaring (`src/compiler/10.frontend/`)~~ — was
misdiagnosed; actual area is test-fixture authoring (host spec files'
own string-interpolation syntax), not the frontend.
**Severity:** medium — corrupted 2 unit-test fixtures; zero production impact
(confirmed: the frontend parser has no defect here)

## Actual root cause (lane IMP1, 2026-07-29)

There is no parser/desugar ambiguity at all. Simple's own double-quoted
string literals interpolate `{expr}` **by default**
(`doc/07_guide/language/syntax.md`: `print "Hello, {name}!"  # Default:
interpolated`). The two red examples wrote the *guest* source under test as
a plain double-quoted *host* string literal containing an **un-escaped**
`{answer}` / `{T32BridgeResult}` — a single bare identifier, which is valid
interpolation-expression syntax. The host spec file's own interpreter
therefore evaluated `answer` / `T32BridgeResult` as an identifier lookup in
the spec's own scope **before the string literal was even constructed**, let
alone passed to `parse_full_frontend` — and since neither name is bound
there, it raised exactly `semantic: variable `X` not found`. Confirmed with
a two-line isolated repro (`val s = "use somemod.{zzzfoo}"` alone crashes,
with no call into the frontend at all).

This also explains the two observations recorded below:
- `use somemod.{a, b}` never crashed: `a, b` is not a valid single
  interpolation expression, so the host lexer leaves the braces as literal
  text instead of attempting to evaluate anything.
- The "named import from module A wins..." example never crashed: it builds
  its source via `+` string concatenation with `open`/`close` variables, so
  no single host string literal ever contains a literal `{identifier}`
  substring for the host's own interpolation to catch — this was NOT
  "context-dependent suppression" of a parser bug, it was simply a fixture
  that happened to dodge the host-interpolation trap by construction.

**Fix:** escape the braces (`\{ \}`) in the two affected fixtures in
`resolve_import_symbols_spec.spl` — `\n` and other escapes still work
normally inside an escaped-brace interpolated string, so no raw-string
(`r"..."`) rewrite was needed. Added
`test/01_unit/compiler/frontend/single_item_use_import_spec.spl` with a
direct minimal repro plus multi-item and aliased-single-item control cases
so a future regression here fails loudly instead of being re-diagnosed as a
parser bug again.

## Original (superseded) finding

## Finding

Calling `parse_full_frontend` directly (bypassing the full driver pipeline,
the pattern used by `test/01_unit/compiler/hir/*_spec.spl` unit specs) on a
source string containing a curly-brace import list with **exactly one** item
crashes with an uncaught runtime error instead of returning a `Module`:

```
semantic: variable `<name>` not found
```

Minimal, 100%-reproducible repro (isolated probe, not the target spec):

```simple
use compiler.frontend.frontend.{parse_full_frontend}
use compiler.common.config.{Logger}

val log = Logger(level: 0)
val m = parse_full_frontend("use somemod.{zzzfoo}", "x1", "x1", log)  # crashes
```

Confirmed crashing shapes (all single-item brace lists):
- `use provider.{answer}` (plain function name)
- `use a.{CompileOptions}` (plain struct/type name) — crashes in isolation,
  though notably did **not** crash inside the full `resolve_import_symbols_spec.spl`
  "named import from module A wins..." example once modules A/B/consumer were
  all parsed together in that exact sequence (see Scope/Open Question below)
- `export use shared.access.{AccessResult as T32BridgeResult}` (aliased
  re-export, still exactly one clause) — crashes with `variable AccessResult
  not found` (the pre-alias name)
- `use compat.types.{T32BridgeResult}` — crashes with `variable T32BridgeResult
  not found`

Confirmed NON-crashing shapes:
- `use somemod.{a, b}` (two-or-more-item brace list) — parses fine
- `use somemod.*` (glob import) — parses fine
- `import somemod` (qualified import) — parses fine

So the trigger is specific to a brace import list with **exactly one** clause,
independent of:
- whether the name refers to a function or a type
- whether the target module ("somemod"/"provider"/"a") has ever been parsed
  in the same process, under the same name, before or after
- whether the imported name was declared anywhere else in the process

## Root-cause hypothesis (not confirmed against source — did not modify
`src/`, out of scope for lane RIS1)

The crash text (`semantic: {0}`) is the Rust interpreter's generic panic
format (`src/compiler_rust/compiler/src/error.rs`), i.e. this is raised while
*interpreting* the frontend's own Simple source for `parse_full_frontend`,
not a `LoweringError` recorded during HIR lowering (which happens later and
separately). The most likely shape: parsing/desugaring a single-clause
`{name}` import list is ambiguous with a one-element expression block/set
literal `{name}`, and some code path evaluates it as a bare identifier
expression rather than an import-list AST node, producing an eager
"undefined variable" panic when nothing named `name` is in scope yet. This is
speculative; the actual defect lives in `src/compiler/10.frontend/core/parser_decls_use.spl`
and/or `parse_full_frontend_with_scope`'s `desugar_module` step
(`src/compiler/10.frontend/frontend.spl`), neither of which this lane
modified or fully traced.

## Open question / scope note

The crash was **not** reproduced for every single-item import in every
context — see `resolve_import_symbols_spec.spl`'s "named import from module A
wins over same-named symbol from module B" example, which uses
`use a.{CompileOptions}` (single-item) and does NOT crash when preceded by
parsing modules "a" and "b" in that specific example's exact call sequence,
yet the identical source string crashes in isolation and in several
variously-reordered isolation probes attempting to match that sequence. The
exact condition that suppresses the crash was not found within this lane's
budget. Re-investigation should instrument `parser_decls_use.spl`'s
`parse_use_decl` (line ~51) directly rather than black-box probing from unit
tests.

## Repro

```bash
cat > /tmp/probe.spl << 'EOF'
use compiler.frontend.frontend.{parse_full_frontend}
use compiler.common.config.{Logger}
describe "probe":
    it "crashes":
        val log = Logger(level: 0)
        val m = parse_full_frontend("use somemod.{zzzfoo}", "x1", "x1", log)
        assert_true(true)
EOF
cp /tmp/probe.spl test/01_unit/compiler/hir/zzz_probe_spec.spl
env -u SIMPLE_TIMEOUT_SECONDS timeout 60 bin/simple test --no-session-daemon test/01_unit/compiler/hir/zzz_probe_spec.spl
# -> "semantic: variable `zzzfoo` not found", exit 1
rm test/01_unit/compiler/hir/zzz_probe_spec.spl
```

## Impact on this lane

`test/01_unit/compiler/hir/resolve_import_symbols_spec.spl` examples
"registers an explicitly imported public function" and "follows an aliased
compatibility re-export to its defining class" fail with this exact crash
and are left red (not weakened) — both examples' harness plumbing was
otherwise repaired correctly (see
`doc/08_tracking/bug/resolve_import_symbols_spec_field_and_wiring_repair_2026-07-29.md`
for the spec-repair summary). This is a genuine product defect blocking
those two examples, not a spec-authoring mistake.

## Related

- `doc/08_tracking/bug/stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`
  — another frontend/HIR receiver-resolution defect surfaced by unit-spec
  isolation of `parse_full_frontend` + `HirLowering`.

## 2026-08-10 — this FIXED status was only HALF TRUE until now

`test/01_unit` and `test/unit` (and `test/02_integration`/`test/integration`)
are duplicate trees and **both execute** — `test_runner_new` has no path
allowlist. The fix recorded above landed on only ONE leg of
`compiler/hir/resolve_import_symbols_spec.spl`. The legacy leg carried 3 \`it\` blocks / 119 lines against the numbered leg's 27 / 750 — five separate bug docs, this one included, all recorded FIXED against a spec whose other executing copy had none of the repairs.
So this document read FIXED while the defect was still live on a tree that
runs on every `bin/simple test`.

Completed 2026-08-10 in commit `6f66d2a6c9885c70fd8fb0163e445cadd0881e1c`, which converges the pair and trims
`scripts/check/test_tree_divergence_baseline.txt` accordingly. Census and
method: `doc/08_tracking/test/half_landed_fixes_across_duplicate_test_trees_2026-08-10.md`.
The class is now fenced: `scripts/check/check-test-tree-divergence.shs`
fails a push whose range edits one leg and leaves the twin divergent.
