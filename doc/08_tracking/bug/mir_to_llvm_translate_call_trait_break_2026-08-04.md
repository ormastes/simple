# `MirToLlvm` no longer satisfies `MirTextCodegen.translate_call` — main is red for every spec

**Status:** FIXED (2026-08-04)
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

---

## Resolution (2026-08-04)

### Re-verified at a later tip — still broken, and WIDER than first reported

Pristine detached worktree at `85b994093c47a0a6ddf1da1a6740a0957089704b`
(`refs/heads/main`, ~9 commits past the tip in the report above), zero
uncommitted `src/`, same seed binary. Verbatim outcome — no `Results:` line
(`grep -c '^Results:'` == 0), aborting on the **last** line of the log:

```
error: semantic: type `MirToLlvm` does not implement required method `translate_block` from trait `MirTextCodegen`
```

Note the method name: `translate_block`, not `translate_call`. The trait check
reports only the **first** missing name in declaration order, and
`translate_block` is declared at `:23`, ahead of `translate_call` at `:31`. So
the original report saw only the tail of the drift. The index/owner-based
rename campaign had actually moved **three** required methods on the sole
implementer:

| trait required (stale) | `MirToLlvm` actually provides |
|---|---|
| `translate_block(block)` (`:23`) | `translate_block_at(blocks, block_index, return_type_text, is_start, return_slot_id)` |
| `translate_terminator(term)` (`:24`) | `translate_terminator_at(blocks, block_index, return_type_text, is_start, return_slot_id)` |
| `translate_call(dest, func, args)` (`:31`) | `translate_call_at(instructions, index)` |

### The fact that decided the fix shape

**`MirToLlvm` is the only implementer of `MirTextCodegen`.** A repo-wide scan
for `impl MirTextCodegen` returns exactly one real hit
(`_MirToLlvm/core_codegen.spl:153`); the only other mention is a *stale comment*
at `c_backend_stubs.spl:7`. `MirToC`, the Lua backend and the WASM/WAT backend
each declare their own `translate_instruction` / `translate_block` /
`translate_terminator` in **inherent** impls (`impl MirToC:` at
`_CBackendTranslate/class_core.spl:57`, `lua_backend.spl`,
`wasm/wat_codegen.spl`) and never route through this trait. Their
`self.translate_instruction(inst)` call sites resolve to their own inherent
methods, not to the trait default.

Consequently the trait's default `translate_instruction(inst)` dispatch has
**zero live callers**: its sole implementer shadows it entirely with
`translate_instruction_at(instructions, index)`
(`_MirToLlvm/core_codegen.spl:553`), whose `case Call` already routes to
`self.translate_call_at(instructions, index)` at `:608`.

A `translate_call` shim on `MirToLlvm` (candidate shape (b)) was ruled out on
evidence rather than taste: it is not even expressible for
`translate_block`/`translate_terminator`, because the `_at` forms need the
owning `[MirBlock]` array plus an index and a detached single block cannot
reconstruct them.

### Change

One file, `src/compiler/70.backend/backend/common/mir_text_codegen.spl`:

1. `:23`/`:24` — required `translate_block` / `translate_terminator` replaced by
   the `translate_block_at` / `translate_terminator_at` signatures the sole
   implementer provides.
2. `:31` — required `translate_call` replaced by `translate_call_at(instructions, index)`.
3. `:67` — the default dispatch's `case Call(dest, func, args)` arm removed. A
   detached-instruction default cannot supply the instruction list and index
   that `translate_call_at` requires, so a `Call` reaching this dead default now
   falls through to the pre-existing `case _: self.translate_unsupported(inst)`
   rather than to a method that no longer exists. Replaced by a comment
   explaining why the arm is absent.

No backend method bodies were touched and no codegen semantics changed — the
change is confined to the trait's required-method list and to a dispatch arm
that no implementer reaches.

### Verification

Same pristine worktree, `SIMPLE_TIMEOUT_SECONDS=0`, `--timeout 3000`, each log
`grep -c '^Results:'` == 1:

| lane | spec | verbatim `Results:` |
|---|---|---|
| 1 | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl` | `Results: 24 total, 24 passed, 0 failed` |
| 2 | `test/01_unit/browser_engine/html_tree_builder_spec.spl` | `Results: 29 total, 29 passed, 0 failed` |

(Lane 2 is 29, matching the figure in the table above; a "26" figure quoted
elsewhere was stale.)

### Standing hazard this leaves

The trait check reports only the first missing name, so a multi-method drift
looks like a single-method break. It is also **name-based only**:
`translate_function` is declared 2-arg at `:22` while `MirToLlvm` defines it
3-arg (`name, body, span`) and `driver_bootstrap.spl:479` still calls it 2-arg —
that arity mismatch passes the check silently today and is deliberately left
untouched here as out of scope for the compile break. It is worth a separate
look.
