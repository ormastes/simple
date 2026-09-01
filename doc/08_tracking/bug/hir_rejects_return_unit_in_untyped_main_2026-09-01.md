# HIR rejects `return ()` in a `fn main():` that declares no return type

- **Date:** 2026-09-01
- **Status:** OPEN — measured, not fixed. Filed rather than worked around, per
  CLAUDE.md ("when a short, safe grammar or compact expression form fails ...
  fix it or record a concrete bug/feature request instead of silently
  normalizing the workaround").
- **Found by:** goal item 2, x86_64 WM host-Vulkan lane, while re-measuring
  `hir_register_imported_symbol_inner_self_bound_to_bool_2026-09-01.md`.

## Symptom

This entry fails phase 3 (HIR lowering):

```
fn main():
    print("hello")
    return ()
```

```
HIR lowering error in <entry>: untyped function returns a value:
function 'main' returns a value but declares no return type; add '-> T'
```

Deleting the `return ()` line makes the same entry lower, monomorphize and
reach codegen.

## Why this is a defect and not just a bad fixture

`return ()` returns UNIT, not "a value". An untyped `fn` already has unit
return type, so `return ()` is the explicit spelling of exactly what the
signature says. The diagnostic's own advice — "add `-> T`" — has no correct
`T` to suggest here.

The shape is **in the tree and load-bearing**, so this is not a hypothetical.
Four tracked files use `fn main():` with no declared return type and a bare
`return ()` in the body:

- `src/app/llm_caret/agent_manager_view.spl` (product code)
- `test/01_unit/compiler/mir/native_build_if_payload_spec.spl`
- `test/01_unit/compiler/mir/native_build_finally_stack_spec.spl`
- `test/01_unit/lib/db/dbfs_device_backed_write_spec.spl`

Note the second and third are **native-build MIR specs** — the very lane this
diagnostic fires on.

There is also a known counter-pressure making the form attractive: a `describe`
block directly in `fn main` exits 1 with a phantom failure, and the recorded
remedy for that is to end `main` with `return ()`. So the codebase has one rule
pushing authors toward `return ()` and HIR rejecting it.

## Cost it has already caused

The repro snippet published in
`hir_register_imported_symbol_inner_self_bound_to_bool_2026-09-01.md` uses this
exact shape. Every run of that documented repro therefore died on the FIXTURE,
not on the defect it was written to isolate — and because the phase-3 failure
branch discarded its diagnostics (fixed separately, see that document's
"Diagnostics-transport defect" section), the real message was invisible. Two
defects compounded into an eight-minute repro that measured nothing.

## Not yet determined

- Whether the reject is in the untyped-return check itself or in how `()` is
  classified upstream of it (is `()` reaching the check as a unit literal, or
  as a value-bearing expression?). The fix belongs wherever `()` stops being
  recognised as unit; do not "fix" this by relaxing the untyped-return check
  generally, which would let genuinely value-returning untyped functions
  through.
- Whether the four files above currently compile on any lane, or are simply
  never native-built.
