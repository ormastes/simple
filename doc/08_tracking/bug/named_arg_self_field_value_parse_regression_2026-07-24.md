# Named-argument value rooted at `self` fails to parse (`Type(field: self.field)`)

**Date:** 2026-07-24
**Severity:** High — breaks the idiomatic immutable-update / builder pattern
`Type(field: self.field, ...)`, reddening previously-green specs.
**Component:** Rust seed parser — labeled/named call-argument value parsing.

## Symptom

Under the currently-deployed `bin/release/x86_64-unknown-linux-gnu/simple`
(48.8 MB, built 2026-07-24 01:22; parser emits the **Rust-seed** form of the
message, incl. the trailing `# self is implicit in methods` comment that the
pure-Simple `recovery.spl:56` copy lacks), a `self`-rooted member expression
used as a **named (labeled) argument value** fails to parse:

```
--> spec.spl:37:19
 37 |     path: self.path,
    |           ^
In Simple, 'self' is implicit in methods. Don't write 'self.'.
```

The `PythonSelf` "self is implicit" message is a **misleading error-recovery
label**, not the real cause — `self.field` reads are valid Simple. The recovery
detector at `src/compiler_rust/parser/src/error_recovery.rs:415` fires on any
`self` `.` pair only *after* the primary parse has already failed.

## Minimal repro (deployed binary, `run` mode)

| # | Snippet (inside a method) | Result |
|---|---|---|
| V1 | `P(a: self.a, b: self.b + 1)` | **PARSE-ERR** |
| V2 | `P(a: src.a)` (non-`self` local root) | OK |
| V3 | `P(a: self.a + 1)` | **PARSE-ERR** |
| — | `self.n * 2` (statement/arith position) | OK |
| W2 | `P(a: cur, b: self.b)` (any labeled arg w/ `self.` value) | **PARSE-ERR** |

So the failure is specific to a **labeled/named argument whose value is rooted
at the `self` keyword**. Positional args and non-`self` roots parse fine, and
`self.field` parses fine everywhere *except* the named-arg value slot.

## Root-cause pointer

- `self` IS a valid primary elsewhere: `expressions/primary/mod.rs:74` (Self_ in
  the primary set) and `expressions/primary/identifiers.rs:17` handle it.
- The labeled-argument disambiguation in
  `src/compiler_rust/parser/src/expressions/postfix.rs:189-254` (speculative
  `parse_expression` then `Colon` check) does not route a `self`-rooted value
  through that primary path, so `label: self.field` mis-parses and drops into
  recovery, which mislabels it `PythonSelf`.
- Fix direction: the named-arg **value** parse must accept a `self`-rooted
  expression exactly as statement-position code does; secondarily, the
  `PythonSelf` recovery heuristic should not fire when `self.` sits in a
  value/expression position (only on a `self.x = …` assignment).

## Affected specs (previously green, now red under this binary)

- `test/unit/compiler/loader/loader_shared_core_spec.spl`
- `test/01_unit/compiler/codegen/spec_constants_contract_spec.spl`
- `test/01_unit/lib/text/utf8_validation_spec.spl`

(Not this bug: `test/01_unit/lib/common/auto_comprehensive_24_spec.spl` fails on
a separate `HIR lowering error: Unknown variable`.)

## Notes / provenance

- `bin/release/x86_64-unknown-linux-gnu/simple` is a **gitignored local
  toolchain artifact** — the origin source of the affected test specs is intact
  and correct; this is a **toolchain regression**, not a source revert. The
  spec fixes remain valid and will go green again once the parser is fixed and
  redeployed.
- The deployed binary running a seed-family parser (Rust-form message) is itself
  a `.claude/rules/bootstrap.md` concern ("default tooling = pure-Simple
  self-hosted, not the seed"). Whether the pure-Simple `recovery.spl` parser
  shares this named-arg limitation is untested here (no self-hosted binary
  currently deployed to compare).
- Do **not** normalize the workaround (rewriting `Type(field: self.field)` to a
  local-temp form) across specs — fix the parser at root per project rules.
