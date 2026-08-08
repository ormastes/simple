<!-- codex-research -->
# Dangerous Comment Grammar Domain Research

Date: 2026-04-23

## Prior Art Summary

Languages and lint ecosystems usually do not trust silent escape hatches. The
common pattern is: allow the construct, but require a precise local explanation
when it suppresses type checking, ignores an error, uses unsafe behavior, or
catches future cases.

## Rust Unsafe Comments

Rust distinguishes safe code from `unsafe` code, and the Rust Reference says
unsafe functions should document extra safety conditions. The Rust standard
library developer guide is stricter: each unsafe block should have a `SAFETY:`
comment explaining why the block is safe and which invariants are relied on.

Sources:

- https://doc.rust-lang.org/stable/reference/unsafe-keyword.html
- https://std-dev-guide.rust-lang.org/policy/safety-comments.html

Design implication for Simple: dangerous comments should capture invariants, not
only intent. For `unchecked(...)`, `raw_pointer(...)`, and FFI conversions, the
required text should answer "what invariant makes this safe?"

## TypeScript and ESLint Suppression Descriptions

`@typescript-eslint/ban-ts-comment` can require descriptions after suppressions
such as `@ts-expect-error`; it also supports minimum description length and
description format patterns. ESLint's `require-description` rule for directive
comments applies the same idea to lint-disable directives.

Sources:

- https://typescript-eslint.io/rules/ban-ts-comment/
- https://eslint-community.github.io/eslint-plugin-eslint-comments/rules/require-description.html

Design implication for Simple: comment requirements should be structured enough
to reject weak placeholders such as `todo`, `fix`, `later`, or `because`.
Minimum useful length and optional issue-code formats are proven controls.

## Go `nolint` Explanations

The Go `nolintlint` analyzer checks malformed or insufficiently explained
`//nolint` directives and can require both the target linter and an explanation.

Source:

- https://pkg.go.dev/github.com/Rodge0/golangci-lint/pkg/golinters/nolintlint

Design implication for Simple: lint suppressions should require both "what is
being suppressed" and "why this suppression is acceptable here".

## Empty Block and Empty Catch Rules

ESLint's `no-empty` rule treats empty blocks as suspicious but accepts blocks
that contain explanatory comments. clang-tidy's `bugprone-empty-catch` warns on
empty catch statements because they hide bugs by swallowing exceptions; it can
ignore catches containing configured keywords such as TODO/FIXME.

Sources:

- https://eslint.org/docs/latest/rules/no-empty
- https://clang.llvm.org/extra/clang-tidy/checks/bugprone/empty-catch.html

Design implication for Simple: no-op paths should be explicit. `pass_do_nothing`
should say why doing nothing is correct; `case Err(_): pass_dn(...)` should say
why the error may be swallowed.

## Wildcard Match Arms

Rust Clippy has a `wildcard_enum_match_arm` lint for enum matches where variants
are covered by `_` instead of explicit arms. Rust Internals discussion around
unmatched variant linting frames the problem: wildcard arms hide newly added enum
variants that should have been reviewed.

Sources:

- https://rust-lang.github.io/rust-clippy/master/index.html#wildcard_enum_match_arm
- https://internals.rust-lang.org/t/pre-rfc-add-an-unmatched-variant-lint/11519

Design implication for Simple: `case _:` is dangerous when matching enum-like,
tagged, protocol, instruction, error, or command types. It should either be
expanded to explicit cases, terminate with a precise error, or carry a rationale
such as `case _("external protocol reserves future opcodes"):` if the grammar
supports it.

## Safety-Critical Switch Defaults

C/C++ safety guidance and tools often require explicit default/switch handling
or warn when default cases are missing. MISRA-oriented material treats switch
coverage and default cases as reviewable safety decisions.

Sources:

- https://clang.llvm.org/extra/clang-tidy/checks/bugprone/switch-missing-default-case.html
- https://www.misra.org.uk/app/uploads/2021/06/MISRA-C-2012-Permits-First-Edition.pdf

Design implication for Simple: the right default depends on type knowledge. For
closed enums, explicit variants are better than `_`; for open protocol values, a
documented catch-all is appropriate.

## Recommended Policy Shape

Use a single "justified escape hatch" model:

- Placeholder: `todo("what remains", "hint or issue")`
- No-op: `pass_do_nothing("why no work is correct")`
- Temporary pass: `pass_todo("what blocks implementation", "next step")`
- Unsafe/invariant: `unchecked("invariant: ...")`
- Suppression: `allow("LINT001", "why acceptable")`
- Wildcard: `case _("why catch-all is correct"):`

The first implementation can support this through lint recognition and string
argument checks. Hard grammar enforcement should be staged behind warn/deny
levels to avoid breaking existing code all at once.

