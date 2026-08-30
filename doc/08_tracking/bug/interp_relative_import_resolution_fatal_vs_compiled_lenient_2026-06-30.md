# Bug: unresolvable relative `import ..` is FATAL in interpret mode, lenient when compiled

**Date:** 2026-06-30
**Severity:** Low — edge case (deprecated `import` syntax + relative path on a
standalone file). Real impact: the two `module_import_spec` examples
"parses import .. as parent" / "parses import ..sibling" fail under the test
runner (interpret mode) but pass compiled.
**Component:** Rust seed — interpreter module resolution
(`interpreter_module/path_resolution.rs:506,862`, `cannot_resolve_module`).

## Asymmetry

A standalone program with a relative parent import:

```simple
import .. as parent
fn main():
    print("relative-parent-ok")
```

- Compiled / default mode: emits a deprecation warning for `import` and a
  resolution warning, then RUNS `main` → exit 0.
- `SIMPLE_EXECUTION_MODE=interpret` (what `bin/simple test` uses): the relative
  path `..` has no parent package, so resolution returns a FATAL
  `Cannot resolve module: ..` → `main` never runs, exit 1.

`module_import_spec.spl` expects the lenient (compiled) behavior: the test is
named "parses import .." and asserts exit 0 + a deprecation-warning string — it
is checking parse + deprecation, not actual resolution.

## Status — RESOLVED (2026-06-30)

All 7 `module_import_spec` failures are now fixed (spec is 21/0). 5 were stale
import paths (commit 69f6b262); the remaining 2 relative-`import ..` cases are
fixed in the seed: `path_resolution.rs` now soft-accepts an unresolvable
relative import (first path segment starting with `.`) by returning the
`UNIT_OPAQUE_SENTINEL` (empty namespace) instead of a fatal `cannot_resolve_module`,
matching the compiled pipeline's lenient warning. Rebuilt + deployed.

Only the secondary finding below remains open.

## Proper fix (needs a design call)

Make interpret-mode relative-import (path starting with `.`) resolution failure
non-fatal (warn + skip), matching compiled mode — scoped to relative imports so
genuine absolute-import typos stay fatal. The fix belongs at the import-statement
evaluator that propagates `cannot_resolve_module`, with relative-path detection,
to avoid masking real unresolved-import errors.

## Related

A secondary seed parse bug was found while fixing the stale paths:
`src/compiler_rust/lib/std/src/core/iter.spl` fails to parse under the seed's
eager `export … from` load path ("expected Newline after impl block colon,
found Identifier Iterator").
