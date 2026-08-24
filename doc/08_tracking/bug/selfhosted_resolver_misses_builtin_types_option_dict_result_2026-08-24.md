# The self-hosted compiler fails to resolve builtin types (`Option`, `Dict`, `Result`) and seed intrinsics (`range`, `fs_has_file_or_dir`, `rt_cpu_count`)

- **Filed:** 2026-08-24 (Lane P, slice A compile census)
- **Status:** OPEN — deliberately NOT "fixed" by adding `use` lines to product code
- **Compiler:** `build/bootstrap/goal-r3/stage2/x86_64-unknown-linux-gnu/simple`
  (132945096 bytes, 2026-08-24 02:50)

## Summary

The single largest real-error class in the 352-file slice-A census. Modules that
the Rust seed bootstraps every day fail HIR lowering under the self-hosted
compiler with `unresolved type:` / `unresolved name:` for names that are builtins
or seed intrinsics, i.e. names the source is correct in not importing.

| unresolved name | occurrences (files) | what it is |
|---|---|---|
| `Option` | 12 | builtin optional type |
| `Dict` | 2 | builtin dictionary type |
| `Result` | 1 | builtin result type |
| `range` | 1 | builtin used by `for i in range(0, n)` across the whole tree |
| `fs_has_file_or_dir` | 1 | seed intrinsic — appears ONLY in the seed's mangle table (`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:1016`), defined in no `.spl` file |
| `rt_cpu_count` | 1 | runtime intrinsic |
| `text_index_of`, `args_push` | 1 each | builtins |

## The compiler diagnoses its own gap

Every affected run first logs, at the *owner* module:

```
[hir-callable-dep-origin-unresolved] owner=compiler.common.error dependency=Option:
  no declaration, re-export hop, or explicit import of this name in the owner;
  a later `unresolved type: Option` will be reported against an importing module instead
```

So the resolver knows the origin is missing, and knowingly defers the failure to
an importing module — which is also why the reported file is often not the file
that needs changing. The diagnostic message itself is good; what is missing is a
builtin/prelude origin for these names on the self-hosted path.

## Why no `use` lines were added

Adding `use` for `Option`/`Dict`/`Result`/`range` to product modules would be
normalising a workaround for a compiler gap, which the house rules forbid: the
source is correct, and the seed compiles it. It would also have to be repeated
across most of the tree. The fix belongs in the self-hosted resolver's prelude /
builtin-origin handling.

## Distinct sub-case: a real layering violation, not a resolver gap

`unresolved type: Value` in `src/compiler/00.common/error.spl` (`TryError(Value)`
at `:120`, `try_error(value: Value)` at `:219`) is NOT this class. `Value` is
declared at `src/compiler/70.backend/backend_types.spl:165` — layer 70 — and is
referenced from layer 00 with no import and no possible one without inverting the
layering. That is a genuine product defect and needs its own decision (move the
type, or change the `CompileError` variant's payload); it is recorded here so it
is not swept into the builtin class and silently "fixed" with a `use`.

## Where detection belongs

**Compiler — it already detects this correctly.** The
`[hir-callable-dep-origin-unresolved]` line and the `unresolved type:` fatal are
precise and actionable. No lint rule or `scripts/check/` gate is warranted; the
only thing missing was that these modules were never compiled. The census is the
detection, and re-running it after a bootstrap redeploy is the regression test.
