# `MirToLlvm` no longer satisfies `MirTextCodegen.translate_call` — main is red for every spec

**Status:** OPEN
**Date:** 2026-08-04
**Severity:** BLOCKER — `bin/simple test` cannot compile *any* spec at current `main`.
**Offending commit:** `0ae43f73ac9` — `fix(compiler): translate bootstrap calls by index`
**Last good commit:** `5687d7fc9558ad8f10756ac9522c8411f3fe7880` (`0ae43f73ac9^`)
**Tip reproduced at:** `48e177f6ccd2efc5c67b404220f2ff6140bfc6e6` (`refs/heads/main`)

## Exact failure

Every `bin/simple test <spec>` run aborts during semantic analysis with no
`Results:` line at all:

```
error: semantic: type `MirToLlvm` does not implement required method `translate_call` from trait `MirTextCodegen`
```

This is not a test assertion failure — it is a hard compile abort in the
compiler's own `.spl` source, which is loaded from source on every run. So it
takes down unrelated lanes (browser-engine / GPU-offload specs below) that have
nothing to do with the LLVM backend.

## Mechanism

`0ae43f73ac9` renamed the method inside `impl MirTextCodegen for MirToLlvm` but
did not update the trait that declares it.

- Trait requirement, still present and now unsatisfied:
  `src/compiler/70.backend/backend/common/mir_text_codegen.spl:31`
  ```
  me translate_call(dest: LocalId?, func: MirOperand, args: [MirOperand])
  ```
- Trait default dispatch, still calling it:
  `src/compiler/70.backend/backend/common/mir_text_codegen.spl:67`
  ```
  case Call(dest, func, args): self.translate_call(dest, func, args)
  ```
- The impl that used to provide it:
  `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:153`
  (`impl MirTextCodegen for MirToLlvm`). In `0ae43f73ac9` its definition became
  `me translate_call_at(instructions: [MirInst], index: i64)` (now at
  `core_codegen.spl:1382`), and `MirToLlvm`'s own dispatch was rewritten to
  `self.translate_call_at(instructions, index)` (`core_codegen.spl:608`).

`mir_text_codegen.spl` was **not touched anywhere** in
`9dcd16644b8..48e177f6ccd`, so the trait contract was left behind by the rename.

After this commit **no type in the tree defines the trait's `translate_call`**.
The only remaining `me translate_call` is
`src/compiler/70.backend/backend/wasm/wat_codegen.spl:700`, which has a
different signature (it takes a `WatBuilder` first) and does not satisfy the
trait. `MirToC` (`src/compiler/70.backend/backend/_CBackendTranslate/class_core.spl`)
does not define it either.

## Why this is left to the refactor's owner

The fix is a trait-contract decision, not a mechanical patch, and it sits inside
an in-flight seven-commit campaign (`039cad933a3`, `9b25558e0af`, `22b04a7b46e`,
`0e052e5f5f8`, `b0ea54dc52d`, `0005061fe47`, `0ae43f73ac9`). The two candidate
resolutions differ in what they imply for the other backends:

1. Drop `translate_call` from the trait's required list and rework the default
   `translate_instruction` dispatch at line 67 — but that default is what
   non-LLVM backends rely on, so `MirToC`/WASM need a dispatch story first.
2. Re-add a `translate_call` shim on `MirToLlvm` that forwards into
   `translate_call_at` — needs a synthetic single-instruction `[MirInst]`, which
   re-introduces exactly the decay hazard the index-based rewrite was meant to
   remove.

Picking either one blind risks silently reverting the campaign's intent, so this
is filed rather than patched.

## Reproduction (pristine, no shared-worktree contamination)

Both runs used a detached `git worktree` with **zero** uncommitted `src/` files,
and the same seed binary (`bin/simple --version` → `Simple Language v1.0.0-beta`,
Rust bootstrap-seed banner — the correct lane for `test`).

```bash
git worktree add --detach <wt> 48e177f6ccd   # tip   -> compile abort, no Results line
git worktree add --detach <wt> 5687d7fc955   # parent -> Results: 24 total, 24 passed, 0 failed
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test \
  test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl --timeout 3000
```

| lane | spec | expected | at `48e177f6ccd` | at `5687d7fc955` |
|------|------|----------|------------------|-------------------|
| 1 | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl` | 24/24 | compile abort | **24 total, 24 passed, 0 failed** |
| 2 | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl` | 47/47 | compile abort | not run |
| 3 | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl` | 38/38 | compile abort | not run |
| 4 | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.spl` | 61/61 | compile abort | not run |
| 5 | `test/01_unit/browser_engine/html_tree_builder_spec.spl` | 29/29 | compile abort | not run |

The lane-1 control at the parent commit passing 24/24 is what pins the
regression to `0ae43f73ac9` specifically, rather than to any of the other ~60
commits in `9dcd16644b8..48e177f6ccd`.

## Note for anyone measuring this

A shared working copy that is behind `main` will show these lanes **green**,
because `.spl` libraries execute from source and a stale checkout still has the
pre-rename `translate_call`. Verify `git merge-base --is-ancestor <tip> HEAD`
before treating a green run as evidence about `main`.
