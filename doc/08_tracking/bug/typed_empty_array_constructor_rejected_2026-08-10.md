# `[i64]()` typed empty-array constructor rejected: "variable `i64` not found"

- **Date:** 2026-08-10
- **Status:** **RESOLVED 2026-08-17** — see the RESOLVED section at the bottom.
- **Binary:** `bin/simple` (self-reports as the Rust bootstrap seed)
- **Lane:** `bin/simple test` (tree-walk interpreter). Native/JIT not probed.

## Symptom

```
val allowed: [i64] = [i64]()
```

fails at spec-execution time with:

```
semantic: variable `i64` not found
```

The example is reported as a normal test failure, not a compile error, so the
construct reads as a runtime defect in the affected example only.

## Reproduction

`test/01_unit/lib/blink/url/url_parser_spec.spl`, `describe "percent_encode"`
(before the workaround was applied). Working spelling: `val allowed: [i64] = []`.

## Scope

10 occurrences of `= [i64]()` exist under `test/` and `src/lib/`. Each is a
latent failure on this lane.

## Unblock condition

Either make the `[T]()` constructor call resolve the element type as a type
(not a variable) in the interpreter's semantic pass, or delete the form from
the language and sweep the 10 call sites.

## RESOLVED 2026-08-17 — root cause and fix

The first option was taken, and taken **in the parser** rather than the
semantic pass, because the defect was never interpreter-specific: `[i64]`
parsed as an ordinary array literal whose single element `i64` was resolved as
a **variable**, and the whole literal was then **CALLED**. Every downstream
lane therefore failed, each in its own vocabulary — the interpreter with
``semantic: variable `i64` not found``, the Cranelift JIT with
`GlobalLoad: unresolved identifier 'i64'`, and the pure-Simple interpreter with
`undefined variable: i64` / `value is not callable`. Recognising the form once
at parse time fixes all of them with a single rule.

Rule: a **zero-argument** call whose callee is a **single-element** array
literal whose element is spelled like a TYPE (a bare name such as `i64` or
`Point`, or a nested array type such as `[i64]`) parses as an empty array
literal. Nothing valid is swallowed — calling an array value is not a legal
operation in any other spelling. `[21]` (not called) and `[x, y]()` (two
elements) are untouched.

Fixed in both frontends:
- Rust seed: `src/compiler_rust/parser/src/expressions/postfix.rs`
  (`parse_call`, helpers `is_typed_empty_array_ctor` /
  `is_array_element_type_expr`). **Requires a rebuilt seed** — a `bin/simple`
  older than 2026-08-17 still reports the original error.
- Pure-Simple compiler: `src/compiler/10.frontend/core/parser_expr.spl`
  (`pe_is_typed_empty_array_ctor` / `pe_is_array_element_type_expr`, applied at
  both postfix call sites, `parse_postfix` and `parse_postfix_on`).

Specs (repro + generalization, mirror-synced into `test/unit/`):
- `test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl` —
  the exact `val allowed: [i64] = [i64]()` repro, pushes into the constructed
  array, and equivalence with the `[]` spelling.
- `test/01_unit/compiler/semantic/typed_empty_array_constructor_general_spec.spl`
  — `f64`/`str`/`bool` element types, a nested `[[i64]]()` element type, a
  user-defined class element type, and a negative case proving a single-element
  VALUE array literal is not intercepted.

### Verification (2026-08-17, controlled A/B in one tree)

Same probe, same tree, only the binary toggled. BEFORE = the deployed
pre-fix seed at `bin/release/x86_64-unknown-linux-gnu/simple`; AFTER = the same
sources built with the parser fix into an isolated `CARGO_TARGET_DIR`
(`cargo build --release --bin simple`, rc=0).

- BEFORE: `rc=1`, `error: semantic: variable \`i64\` not found`, preceded by the
  Cranelift JIT bailing out on the same identifier — zero assertions reached.
- AFTER: `rc=0`, **11 of 11 PASS**, and no JIT-failure line at all (so the JIT
  lane compiles the form now, it does not merely fall back). Cases: the `[i64]()`
  repro, push/read-back, `[]`-spelling equivalence, `f64`/`str`/`bool` element
  types, nested `[[i64]]()`, a user-defined class element type with field
  read-back, and the negative case (`[21]` still a value array literal).
- `sh scripts/check/check-jit-unresolved-symbol-guard.shs` with the rebuilt
  binary: `PASS — 6 lane-cases checked`, confirming the repointed fixture below
  still diagnoses on both lanes.
- `cargo check --release --bin simple`: clean (3 pre-existing warnings, 0 errors).

Note that `bin/simple test` was **not** usable as evidence here: on this spec it
exhibits the known silent-green defect (~1900 warning lines, no results line) or
is killed by the CPU monitor. Per `.claude/rules/testing.md`, that is
INCONCLUSIVE, so the behaviour was confirmed by direct `run` repro instead.

Fixture note: `test/fixtures/jit_unresolved_symbol_guard/typed_ctor.spl`
previously used `[i64]()` as deliberate BAD INPUT. That form is now valid, so
the fixture would have failed open (rc=0, `SHOULD_NOT_PRINT`). It was repointed
to a **two-element** array-literal callee (`[no_such_symbol_here, 2]()`), which
the constructor rule never intercepts, preserving the guard's actual intent:
an unresolved symbol must DIAGNOSE on both the interpreter and JIT lanes.
