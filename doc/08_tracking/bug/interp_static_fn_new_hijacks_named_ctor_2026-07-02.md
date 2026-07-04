# Interpreter: `static fn new` hijacks named-argument class construction

Date: 2026-07-02
Status: open (workaround in place for Font)
Severity: P1 (silent wrong-field construction)
Found by: W8 lane agent while building game2d event replay specs

## Symptom

Any class declaring `static fn new(...)` makes the named-argument
constructor form `Class(field: value)` bind the named args against `new`'s
parameter list instead of the class fields:

- Mismatched names fail: `error: semantic: unknown argument 'id'`.
- Overlapping names are WORSE — `Font(path: "x", size: 8)` "succeeds" but
  produces `Font(id: nil, size: nil)`: silent nil-field corruption.

Minimal repro: class `Widget` with fields `id, size` plus
`static fn new(path, size)` → `Widget(id: 3, size: 4)` fails to bind.

Binder: `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs`
("unknown argument").

## Impact

Every class in the tree that keeps a `static fn new` with non-field params
constructs corrupt instances via the named form. `Font.default_font()`
(called by `Canvas.create` → `begin_frame` every frame) was dead on
arrival until the workaround.

## Workaround

`game2d/render/font.spl`: renamed caller-less `static fn new(path, size)`
→ `static fn load` (2026-07-02). House style already prefers named
constructors over `.new()` (see .claude/rules/language.md), so remaining
`static fn new` declarations should be audited/renamed.
