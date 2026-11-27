# `.?` on `Some("")`: interpreter says present, JIT says absent

- **Date:** 2026-11-06
- **Status:** open
- **Severity:** P2 (engine divergence)

## Defect

0b3c5ae9e36 made the seed interpreter treat `Some("")` as present, per
`syntax_quick_reference.md:593-596`: an optional passes through unchanged, and a bare `""`
is absent. The JIT lane still reports `Some("")` as absent. Also inconsistent:

- `Ok("")` is reported absent.
- `val t: text? = ""` is absent in both lanes.

So presence currently depends on how the value is stored, not just on its type.

## Fix direction

Decide and document the rule for `text?` and `Result` presence, then make the JIT `.?`
lowering match the interpreter.
