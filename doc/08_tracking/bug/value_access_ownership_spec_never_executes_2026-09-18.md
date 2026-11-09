# The compiler runtime-value-accessor ownership spec has never executed, and it is hiding a contradiction with the audit script that replaced it

- **id:** value_access_ownership_spec_never_executes_2026-09-18
- **status:** OPEN
- **severity:** P2 — a guard that reports nothing is indistinguishable from a guard that passes, and this one would FAIL if it ran
- **found:** 2026-09-18, while deleting the orphaned `_MirLoweringExpr/literals.spl`
  (`duplicate_impl_method_definitions_silent_first_wins_2026-08-08.md`)

## Symptom

`test/01_unit/compiler/mir/value_access_ownership_spec.spl` declares three
examples and executes **zero**:

```
error: runtime: Module "compiler.common" does not export 'value_access'
error: test-runner: no examples executed
SPEC FILE VERDICT: ... outcome=ERROR declared>=3 executed=0 passed=0 failed=0
```

Its third import line is:

```simple
use compiler.common.value_access.{compiler_value_discriminant, compiler_value_payload, compiler_value_tuple_at}
```

and **no `value_access.spl` exists anywhere under `src/`** (`find src -name
'value_access*.spl'` returns nothing; `src/compiler/00.common/__init__.spl` names
it nowhere). The module the spec is built on is gone, so the file cannot load and
the spec has been inert for however long that has been true.

## Why it matters more than an ordinary red

The spec's job is to own an invariant: nothing in the listed compiler files may
reach for the raw runtime value accessors directly. Its helper asserts, for each
of eight compiler source files, that the file contains none of
`extern fn rt_enum_discriminant(`, `extern fn rt_enum_payload(`,
`extern fn rt_tuple_get(`, or a bare call to any of the three.

**That assertion is false today for at least one of the files it names.**
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` contains exactly
one `extern fn rt_enum_discriminant(`. So were the spec loadable it would fail
immediately.

Worse, another live guard asserts the **opposite** and is satisfied:
`scripts/audit/compiler-mir-method-sffi-authority.shs` requires

```sh
test "$(rg -c '^extern fn rt_enum_discriminant\(' "$module")" -eq 1
```

on that same file. One guard requires exactly one occurrence; the other requires
zero. They cannot both be right, and nobody has had to choose, because the one
that would object cannot run.

## What needs deciding, not just fixing

Making the spec load is the easy half and the wrong half to do alone — it would
turn a silent contradiction into a red without settling which guard states the
real rule. The ownership question has to be answered first:

1. Is the MIR method-lowering file **allowed** one direct `rt_enum_discriminant`
   declaration (the audit script's position, and the tree's current state)? Then
   the spec's file list is stale and that file should come off it, with the reason
   recorded.
2. Or is the ownership rule absolute (the spec's position)? Then the declaration
   in `method_calls_literals.spl` is debt to be routed through the canonical
   owner, and the audit script's `-eq 1` is the stale line.

Either way the `compiler.common.value_access` import must be repaired or dropped,
since the module it names does not exist. Note that the spec's first example
(`preserves typed enum discriminant and tuple-payload semantics`) is the only
consumer of those three imported functions; the two ownership examples need no
import at all and could load today if the import were scoped to the example that
uses it.

## Related

- `duplicate_impl_method_definitions_silent_first_wins_2026-08-08.md` — found
  during its resolution; that record's deletion removed this spec's ninth file
  entry, which is what surfaced the load failure.
- The repo's own standing principle that a check which examined nothing is an
  ERROR and never a pass (`.claude/rules/vcs.md`, every `scripts/check/` guard's
  verdict convention). This spec predates that convention and does not follow it:
  the runner reports `no examples executed` rather than the suite treating a
  declared-but-unloadable spec as a hard failure.

## 2026-11-09 — fix-implemented-verification-pending (owner decision: no exception)

Owner ruled option 2: the ownership rule is absolute. `method_calls_literals.spl`
gets no exception; the audit script's `-eq 1` was the stale line.

What landed:

- **Canonical owner created:** `src/compiler/00.common/value_access.spl` — the
  module the spec always imported but which never existed in the tree (no git
  history). It is the single declaration site for `rt_enum_discriminant`,
  `rt_enum_payload`, `rt_tuple_get` and exposes the typed inline wrappers
  `compiler_value_discriminant<TEnum>`, `compiler_value_payload<TEnum, TPayload>`,
  `compiler_value_tuple_at<TElement>`. Added to
  `scripts/check/no_direct_rt_allowlist.txt` (owner+reason: this record).
- **Routed:** `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
  and `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (which also
  carried three externs plus three bare `rt_enum_discriminant(` calls) now import
  the owner and declare no runtime extern. Their `_sffi_*` inline helpers are
  kept as names and delegate to the owner.
- **Audit:** `scripts/audit/compiler-mir-method-sffi-authority.shs` now requires
  0 declarations / 0 direct calls / 0 `unsafe` blocks in the MIR module, the
  owner import, and exactly one declaration of each accessor in the owner. It
  was switched from `rg` to `grep -cE` because `rg` is absent on the Windows
  host (the script had never run here; its `_sffi_method_hir_type_discriminant(`
  count of 3 was already stale — the real line count is 8).
- **Spec:** `test/01_unit/compiler/mir/value_access_ownership_spec.spl` executes.
  Example 3 now asserts the two routed MIR files only; the design-fiction lines
  (`val binary_op: HirBinOp = compiler_value_tuple_at(...)` etc.) that never
  existed in `expr_dispatch.spl` were dropped.

Evidence (seed `C:/dev/simple/bin/simple.exe test`, cwd = lane worktree):

```
RED   outcome=ERROR declared>=3 executed=0  error: runtime: Module "compiler.common" does not export 'value_access'
GREEN outcome=OK    declared>=3 executed=3 passed=3 failed=0
FLIP  (method_calls_literals.spl reverted to origin) outcome=ERROR executed=3 passed=2 failed=1; audit rc=1
```

### Remaining debt (direct raw-ABI readers, not yet asserted by the spec)

The original spec's third example named six more files as clean; none of them
is. Direct `rt_enum_discriminant(`/`rt_enum_payload(`/`rt_tuple_get(` sites
measured 2026-11-09: `10.frontend/parser_types_expr.spl` 48,
`50.mir/_MirLowering/module_lowering.spl` 9, `10.frontend/parser_types.spl` 7,
`50.mir/mir_lowering_stmts.spl` 7, `50.mir/_MirLowering/function_lowering.spl` 2,
`50.mir/_MirLoweringExpr/switch_operators_calls.spl` 2. Routing them through
the owner is the same mechanical change as this lane's; each file should be
added to the spec's example 3 as it is routed.
