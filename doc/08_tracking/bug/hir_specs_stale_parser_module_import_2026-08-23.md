# HIR specs import a symbol that does not exist and have never executed

- **Filed:** 2026-08-23
- **Status:** OPEN
- **Layer:** `test/01_unit/compiler/hir/**` (and its `test/unit` mirror)
- **Found by:** AST -> HIR construct census, `doc/09_report/hir_construct_coverage_matrix_2026-08-23.md`

## Summary

`test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl` -- the spec covering
the exact defect class that produced 1412 stage1 errors from one hardcoded field-visibility
line -- imports `compiler.frontend.parser_types.Module`. No such symbol exists: the struct
is `ParserModule` (`src/compiler/10.frontend/parser_types.spl:21`), and
`/usr/bin/grep -rn '^struct Module:' src/compiler/10.frontend/` returns nothing.

The spec therefore ERRORS before executing a single example, and has been doing so silently:

```
SPEC FILE VERDICT: test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl \
  outcome=ERROR declared>=15 executed=0 passed=0 failed=0 skipped=0 dropped=0
error: runtime: Module "compiler.frontend.parser_types" does not export 'Module'
error: test-runner: no examples executed
```

`declared>=15 executed=0` is the tell: fifteen declared examples, zero ever run. A visibility
regression could not have been caught by it at any point.

## Second, independent defect in the same file

Every call site passes the arguments transposed:

```
parse_full_frontend(provider_source, provider_name, provider_path, log)
```

against the real signature
`parse_full_frontend(source: text, file_path: text, module_name: text, log: Logger)`
(`src/compiler/10.frontend/frontend.spl:168`). Module name and file path are swapped. Fixing
only the import would leave the spec exercising the wrong module identity -- which is the
very axis re-export and facade-hop resolution depends on.

## Scope not yet established

Only this file was confirmed. The other 176 specs under `test/01_unit/compiler/hir/` and
`.../frontend/` have NOT been swept for the same stale import; the `declared>=N executed=0`
verdict shape is the mechanical signal to sweep for. Recorded here rather than claimed fixed.

## Fix

Rename the import to `ParserModule`, correct the argument order at every call site, and
confirm the verdict moves from `executed=0` to `executed=15`. Deliberately NOT done in the
change that filed this: it is a behaviour change to a spec another lane may own.
