# Cross-module call cannot construct its own enum payload (`Expected` not found in this scope)

**Date:** 2026-08-22
**Status:** OPEN
**Spec:** `test/03_system/compiler/parser_spec.spl` — scenario `is a documented feature` (RED, correctly failing)

## Reproduce

```bash
bin/simple test test/03_system/compiler/parser_spec.spl
# ✗ is a documented feature
#   semantic: enum `Expected` not found in this scope
```

## Defect

`std.doctest.parser.parse_docstring` (`src/lib/common/doctest/parser.spl:55`)
returns `[DoctestItem]` whose `expected` field is the enum `Expected` (defined
in the same module). Calling it from a spec file with a docstring that
CONTAINS a `>>> ` example fails with `semantic: enum Expected not found in
this scope`; calling it with a docstring containing no examples (returns
`[]`, never constructs the payload) succeeds. The failure occurs only on the
path where the callee must construct its own enum value for the caller — the
enum's name is not resolvable at the call site even with
`use std.doctest.parser.*`.

This blocks every spec that wants a real oracle over doctest parsing.

## Unblock condition

Cross-module enum construction from a callee must resolve the enum from the
callee's module scope, not require it at the caller's scope.

## Tests

- Reproducing spec: `test/03_system/compiler/parser_spec.spl` (scenario above).
- Neighbor (same pattern, passes because payload never constructed): the
  `will be tested when module imports are stable` scenario in the same file.
