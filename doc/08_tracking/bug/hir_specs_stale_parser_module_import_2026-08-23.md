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

---

## Update 2026-08-23 — execution sweep of all 227 HIR/frontend/transition specs

The original record said the scope was unswept. It has now been swept **by execution**,
which is the authority on `executed=0` (static resolution cannot prove absence).

Every `_spec.spl` under `test/01_unit/compiler/{hir,frontend,transition}` was run
individually and its `SPEC FILE VERDICT` line parsed for `declared>=N executed=M`.
3 workers only, because the host was saturated by other lanes (load 39 on 32 cores,
137 concurrent `simple` processes, 8 GB free) and this sweep must not disturb them.

### Result

227 specs run. Final tally:

| outcome | count |
|---|---|
| `outcome=OK` (executed, all passed) | 163 |
| executed but FAILED | 61 |
| `declared>0` with `executed=0` (phantom verdict) | 1 |
| no verdict at all, `rc=124` (timed out at 600 s) | 2 |

**Two specs total carry the phantom-verdict defect**, both on the identical cause:
`use compiler.frontend.parser_types.Module`, where the struct is `ParserModule`
(`src/compiler/10.frontend/parser_types.spl:21`).

The table above counts only **one**, because `member_visibility_enforcement_spec.spl` was
already fixed in the working tree by the time the sweep reached it — its row therefore
records the post-fix `rc=124` state, not the original `executed=0`. Stated explicitly so
the 1 is not mistaken for the population.

| spec | before | after fix |
|---|---|---|
| `frontend/single_item_use_import_spec.spl` | `declared>=3 executed=0` ERROR | `declared>=3 executed=3 passed=3` **OK** |
| `hir/member_visibility_enforcement_spec.spl` | `declared>=15 executed=0` ERROR | import resolves; now **times out** — see below |

Neither has a `test/unit/` mirror twin, so no divergence risk.

### Second, independent finding: a pre-existing hang I did not cause

`test/01_unit/compiler/hir/module_surface_declaration_authority_spec.spl` also produced
**no verdict, `rc=124`**. It is untouched by this change (`git diff HEAD -- <path>` is empty)
and its import set is clean, so this is an independent pre-existing hang in a spec covering
module-surface declaration authority — adjacent to the re-export/facade-hop class. Not
diagnosed here. Left RED.

### Third finding: the failure rate in these trees is 27 %

61 of 227 specs executed and FAILED, on top of the 2 that hang and the 2 phantom verdicts.
That is 28 % of the HIR/frontend/transition unit corpus not green. This is a much larger
signal than the phantom-verdict class itself and is NOT triaged here — recorded so it is not
lost. The raw per-spec table (path, declared, executed, outcome, rc, first runtime error) is
at `/mnt/data/tmp/hir_frontend_spec_execution_sweep_2026-08-23.tsv` (227 rows).

### Correction to a sibling lane's characterisation

A parallel static scan reported that `member_visibility_enforcement_spec.spl` fails on
**all five** of its module imports and that their parents do not exist. That is a false
positive. `single_item_use_import_spec.spl` carries the same import set
(`std.spec`, `compiler.common.config.Logger`, `compiler.frontend.frontend.parse_full_frontend`,
`compiler.common.driver_core_types.SourceFile`, `compiler.hir.hir_lowering.*`), and changing
**only** `Module` -> `ParserModule` took it from `executed=0` to `executed=3 passed=3`. If any
other import were unresolvable it could not have executed at all. The same import set is also
used by the new `ast_to_hir_construct_coverage_spec.spl`, which runs 71/71. Exactly one import
is broken, not five.

### New finding: the import error was hiding a hang

With the import fixed, `member_visibility_enforcement_spec.spl` no longer errors — it reaches
the real lowering and does **not complete**. Two independent measurements, the second run
ALONE so host contention cannot explain it:

```
# under the 3-worker sweep, 600 s wall cap
  rc=124, no verdict emitted

# isolated, nothing else of mine running, runner's own 900 s budget
SPEC FILE VERDICT: .../member_visibility_enforcement_spec.spl declared>=1 executed=1 \
  passed=0 failed=1 dropped=0 timeout=1 reason=child-timeout budget_ms=900000
```

`reason=child-timeout budget_ms=900000` is the runner's own verdict, not my wrapper's: the
spec exceeds **900 s** in isolation. That is a hang, not slowness under load. The unresolvable import was masking a second,
independent defect underneath it. Fixing the import is still strictly correct — an import
naming a type that does not exist is unambiguously wrong — but it converts a silent
`executed=0` into an honest RED/timeout, which is the point.

The timeout is NOT diagnosed here and the spec is left failing. Do not tag it, skip it, or
delete it to get green.

### Method limitation, stated

A static `use`-target resolver was tried first and **missed the control**: it accepts a member
whose name appears as a whole word anywhere in the resolved module, and `Module` appears in
`parser_types.spl` prose. In strict mode (defined names only) it caught the control but
produced false positives on symbols that do resolve (e.g. `SourceFile`). Static scanning is a
useful prefilter and is ~200x cheaper, but on this defect class only execution is decisive.
