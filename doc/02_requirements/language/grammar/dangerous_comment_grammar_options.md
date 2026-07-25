<!-- codex-research -->
# Dangerous Comment Grammar Feature Options

Date: 2026-04-23

## Option A: Lint-First Required Rationales

Add production wiring for `required_comment`, extend it to `pass`, `todo`, and
wildcard arms, and keep existing grammar mostly intact.

Requirements:

- `pass`, `pass_todo`, `pass_do_nothing`, and `pass_dn` without a non-empty
  rationale warn through both parser and `bin/simple lint`.
- `todo(...)` is recognized by lint as a placeholder escape hatch. Missing or
  weak text warns with a hint to state "what remains" and "next step".
- `case _:` warns unless the arm body is an explicit failure/unsupported path or
  has a local rationale comment.
- Dangerous calls from the registry require a first string rationale.

Pros:

- Lowest compatibility risk.
- Fixes current missing path where `check_required_comment()` is not wired.
- Gives measurable warnings before grammar changes.

Cons:

- Syntax remains less crisp than `case _("why"):` until later.
- Comment association for wildcard arms may be heuristic.

Effort: M, about 5-8 files.

## Option B: Grammar-Level Justified Escape Hatches

Introduce explicit grammar forms for justified dangerous constructs.

Requirements:

- `todo("what remains", "hint")` becomes first-class syntax.
- `case _("why catch-all is correct"):` becomes the preferred wildcard arm form.
- `pass("why")`, `pass_todo("what remains", "hint")`, and
  `pass_do_nothing("why no-op is correct")` become the preferred forms.
- Bare forms continue with warnings for one compatibility window.

Pros:

- Clear language-level contract.
- Avoids fragile comment attachment.
- Makes generated code and easy-fixes straightforward.

Cons:

- Requires parser, AST, formatter, docs, and test changes.
- Existing examples may need broad cleanup.

Effort: L, about 10-16 files.

## Option C: Safety Profile With Deny-by-Default Escape Hatches

Create a configurable safety profile that denies unjustified dangerous constructs
outside tests and generated code.

Requirements:

- Builds can enable `safety_profile = "strict"` in `simple.sdn`.
- In strict mode, unjustified `pass`, `todo`, wildcard arms, unchecked/raw/unsafe
  calls, and lint suppressions are hard errors.
- Default project mode remains warn while the codebase is migrated.

Pros:

- Good fit for compiler/core/lib, OS, driver, FFI, MCP/LSP hot paths.
- Lets examples and early prototypes move more gradually.

Cons:

- More config and documentation.
- Requires path classification for tests/generated/production.

Effort: L, about 8-14 files.

## Option D: Comprehensive Dangerous Construct Registry

Make dangerous constructs data-driven through a registry with categories,
required rationale fields, examples, lint code, and default severity.

Requirements:

- Registry covers placeholders, no-ops, wildcard arms, unsafe/raw/unchecked
  calls, FFI/asm escape hatches, lint suppressions, and swallowed errors.
- Each category defines required wording: what, why, invariant, next step, issue,
  or unsupported path.
- Lints use the registry for messages, hints, and docs generation.

Pros:

- Scales beyond pass/todo without ad hoc rules.
- Produces consistent diagnostics and docs.

Cons:

- More abstraction than needed for the first fix.
- Needs careful ownership to avoid becoming a dumping ground.

Effort: XL, about 14-24 files.

## Recommendation

Start with Option A plus the `todo` and wildcard parts of Option B. That fixes
the current broken warning path quickly while preserving a route to explicit
grammar once warning volume is known.

