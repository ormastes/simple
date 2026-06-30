# SCV Feature Requirement Options

Status: option record, 2026-05-14.

## Option A: Byte-Exact Core With Parser-Aware Derived Views

Description: Store exact file bytes first. Build parser, syntax, semantic, whitespace, diff, merge, and compression views as derived indexes.

Pros:

- Preserves all work when parsers fail, grammars change, or file types are unsupported.
- Matches the user's requested architecture.
- Allows jj-like private savepoints without blocking on language tooling.
- Keeps Git-compatible raw file behavior possible.

Cons:

- More layers to design than a parser-only system.
- Structural diff/merge arrives after raw storage.

Effort: high.

Decision: selected by user direction.

## Option B: AST-First VCS

Description: Store syntax nodes as the primary repository object model.

Pros:

- Simple conceptual path to semantic diff.
- Good compression for supported languages if parsing succeeds.

Cons:

- Loses or degrades unsupported files.
- Parser and grammar version changes can alter repository identity.
- Unsafe for syntax errors and binary files.

Effort: high.

Decision: rejected.

## Option C: Git Wrapper With Better UX

Description: Wrap Git/Jujutsu with a new command surface.

Pros:

- Fastest initial CLI.
- Reuses mature Git storage.

Cons:

- Does not implement SCV's requested byte/parser/structural model.
- Existing `sj` already covers much of this wrapper role.

Effort: medium.

Decision: rejected for SCV core.
