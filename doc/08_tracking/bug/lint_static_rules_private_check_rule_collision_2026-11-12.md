# Static lint rules sharing a private `fn check_rule` dispatch into each other

**Status:** LINT RULES FIXED 2026-11-14 (unique `<rule>_check_rule` names); UNDERLYING RESOLVER DEFECT STILL OPEN (compiler/seed owner). Originally observed 2026-11-12 while landing `robust_option_surface` (P1), which sidestepped it by naming its check fn uniquely.
**Severity:** Correctness of the live lint table (findings attributed to the wrong rule; some rules silently emit nothing).
**Affected files:** 15 of `src/compiler/90.tools/lint/rules/*.spl` declare a private `fn check_rule(params: LintParamsV1, unit: LintUnit)` (e.g. `nil_outside_unsafe_rule.spl:175`); `nil_return_non_optional_rule.spl:447` and `robust_option_surface_rule.spl` already use a unique name.
**Spec files:** `test/01_unit/compiler/lint/static_rule_dispatch_identity_spec.spl` (guard: row identity, full-table once-only, private fn-name uniqueness across rule modules).

## Symptom

With the seed as the engine, running the full `static_lint_rule_table()` on
`pub fn connect(host: i64, timeout: Option<i64>) -> i64:` + `return nil`
emitted `ROB-OPT-001` 16 times (once per sibling whose `check_rule` resolved
to the newest module's `check_rule`) and never `NIL-UNSAFE-001`, while each
rule run alone through its own import path behaved correctly. The seed
prints the matching banner at startup:
`public function ... has N co-compiled definitions ... call sites resolve by
the caller's import path ... Rename the conflicting helper(s) to a unique
name. [compiler_cross_module_private_symbol_collision]`.
Renaming the new rule's fn to `robust_option_surface_check_rule` dropped the
count to one, which proves the mechanism.

## Unblock condition

Give every rule's check fn a unique name (`<rule>_check_rule`), then add a
spec that runs the full table on one fixture and asserts each code appears
exactly once; and a generalization spec asserting `NIL-UNSAFE-001` fires
through the full table (today it does not).

## Reproduction on 2026-11-14 (release/1.0.0 tip `6ecc57c5ae8`, Rust seed `bin/simple.exe`)

A spec that imports `compiler.tools.lint.rules.nil_outside_unsafe_rule.{nil_outside_unsafe_lint_rule}`
directly, then runs every row of `static_lint_rule_table()` alone on
`fn f() -> i64?:\n    nil\n`, gets `NIL-UNSAFE-001` from **15** rows:
`accessor_parent_name, bare_primitive_internal, const_ref_default,
constant_interpolation, cow_alias_hotpath, leading_operator,
linear_scan_in_loop, module_init_literal, nil_outside_unsafe, nogc_ownership,
nonexistent_type, panic_free, raw_sffi, riscv_debuggability,
unwrapped_foreign_resource` — exactly the 15 modules with a private
`fn check_rule`. The two uniquely named rows (`nil_return_non_optional`,
`robust_option_surface`) and the rows whose check fn already had another name
behave correctly. So the winner is the module the caller imported; without
that direct import (only `static_rules`), the same fixture produced no
`NIL-UNSAFE-001` from any row (a different `check_rule` body won).

## Fix (lint side, 2026-11-14)

Each of the 15 rule modules now names its check fn `<rule>_check_rule`
(precedent: `robust_option_surface_check_rule`,
`nil_return_non_optional_check_rule`); the `static_lint_rule(...)` reference in
the same file was updated. `static_rules.spl` imports only the public
`*_lint_rule()` constructors, so the table needed no change; no spec imported
the private `check_rule`.

Guard spec `static_rule_dispatch_identity_spec.spl`: before the renames 1/4
passed (NIL-UNSAFE-001 emitted by 15 rows, 15 times through the full table,
14 private `check_rule` clashes); after, 4/4 pass.

## What remains (compiler / seed owner)

The resolver defect itself is NOT fixed: a reference to a **private**
top-level function (`check_rule`, passed as a fn value) inside module A
resolves to a same-named, same-signature private function in co-compiled
module B — chosen by the caller's import path — instead of A's own
definition. Private functions should never be visible across modules, so the
in-module reference must always bind to A's definition. The seed's
`[compiler_cross_module_private_symbol_collision]` banner (≈140 same-signature
names per run) shows the class is wider than lint rules. Repro for the owner:
revert any one rename above (or add two modules each with
`fn check_rule(params: LintParamsV1, unit: LintUnit) -> [StaticLintFinding]`
returning different codes, each wrapping it in a `pub fn ..._lint_rule()`),
import one of them directly from a spec, and run the other's row: it emits the
imported module's code. The guard spec's fn-name-uniqueness case keeps the
lint rules safe until that is fixed; remove the workaround names only after
the resolver binds private names module-locally.
