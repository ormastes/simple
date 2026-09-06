# Pure-Simple frontend parser rejects `actor` declarations (Rust seed accepts them)

**Date:** 2026-09-05
**Found by:** sspec score-80 wave 2 (modernizing `test/unit/compiler/parser/parser_actor_spec.spl`)

## Symptom

The same actor source takes two different paths with opposite verdicts:

| path | verdict |
|---|---|
| `parse_module("actor Counter:\n    var count: i64 = 0\n", ...)` from `src/compiler/10.frontend/core/parser.spl:1132` (pure-Simple frontend, in-repo) | parse ERROR — `line 1:14: unexpected token in expression: ':'`, `parser_has_errors()` true |
| `./src/compiler_rust/target/bootstrap/simple run <file with the same decl>` (Rust seed run path) | parses clean (only complaint is "no `main` function") |

Control: `class Counter:` through the same pure-Simple helper parses clean
(`parser_has_errors()` false). Reproduced 2026-09-05 with a two-statement probe
through both paths.

## History that hid it

The pre-wave-2 spec asserted "actors parse" via tautology filler
(`expect(1).to_equal(1)`), so it passed 16/0 vacuously while the pure-Simple
parser never supported the decl. The modernized spec now asserts the CURRENT
fail-closed behavior (actor forms are reported as errors, never silently
mis-parsed) so the file is an honest executable record — but the underlying gap
remains: the language supports actors (reserved keyword, `desugar_actor`
transform, Rust seed parses them) and the pure-Simple frontend parser does not.

## Fix direction

Add actor-declaration parsing to `src/compiler/10.frontend/core/parser.spl`
 mirroring the Rust seed's grammar (see `src/compiler_rust/parser/`), then
flip the three `rejects … actor …` scenarios in
`test/unit/compiler/parser/parser_actor_spec.spl` and its
`test/01_unit/...` twin back to positive parse-and-spawn assertions.

## Unblock condition

Pure-Simple `parse_module` accepts `actor`, `pub actor`, and `actor T<...>`
forms without errors; spec twins updated to assert the positive contract.
