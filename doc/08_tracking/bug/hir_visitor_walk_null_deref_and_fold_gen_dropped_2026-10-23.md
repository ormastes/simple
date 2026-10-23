# `hir_visitor.walk_hir_type` dereferences a raw NULL, and `fold_gen.spl` had lost the four functions needed to regenerate it

- **Date:** 2026-10-23
- **Status:** OPEN (the NULL deref) / FIXED (the dropped generator functions)
- **Blocks:** Stage 2 admission on `release/1.0.0`, and therefore any full bootstrap

## Why this record exists

An earlier commit of mine said this was "filed separately" when it was not.
Nothing in `doc/08_tracking/bug/` or `bug_db.sdn` mentioned `walk_hir_type`,
the `hir_visitor` NULL dereference, or `prepare_fold_inputs`. This is that file.

## 1. The crash (OPEN)

With the codec payload-bind SIGSEGV fixed (#4232), the stage-2 sanity battery
advances past `module_path_naming` and dies in the generated HIR visitor:

```
#0  compiler.hir.generated.hir_visitor.walk_hir_type ()     <-- SIGSEGV
#1  walk_hir_expr
#2  walk_hir_stmt
#3  walk_hir_block
#4  semantics.representation_boundary.unsafe_observations.representation_observe_function_v1
#5  representation_missing_manifest_observations_v1
#6  driver.hir_semantic_consumer_v1.collect_module_representation_receipt_v1
#7  driver.driver_hir_pipeline_passes.run_representation_manifest_pass
si_addr = 0x0
```

**`si_addr` is `0x0` — a raw NULL, NOT nil's immediate `0x3`.** That distinction
is the whole point of this record, because it rules out the obvious fix:

- the prologue guard is `if node == nil: return ctx` (emitted by
  `src/app/compiler_schema/fold_gen.spl`), and `== nil` compares against nil's
  *immediate* (3), so a raw NULL (0) does not match and `node.kind` dereferences 0;
- **but swapping it to `.?` does NOT fix it either.** `.?` lowers to
  `rt_is_some`, and `src/runtime/runtime_native.c:5612-5616` treats a raw zero
  word as a **valid present payload** ("raw zero remains a valid present
  payload"). So `.?` reports present for `0` and the dereference still happens.

A correct guard has to reject a zero word specifically. The codec's own callee
prologues do this with `rt_heap_ref_wellformed(node)`, which has a zero-page
reject — that is why the codec path degrades to a refused module rather than a
crash. Emitting that into the generated visitor means the generator emitting a
raw `rt_*` extern, which `.claude/skills/spipe.md` gates behind a recorded
`runtime_need` / `facade_checked` / `chosen_path` decision. That decision has
NOT been made, which is why this record stops here rather than guessing.

Open question for whoever takes it: where does a raw NULL `HirType` enter a
lowered module in the first place? `representation_observe_function_v1` walks
every function, so the producer is upstream of the visitor; guarding the walker
makes the symptom fail-safe but does not explain the NULL.

## 2. The generator could not run at all (FIXED here)

`main.spl visitors` and `main.spl folds` both failed with:

```
error[E1002]: function `prepare_fold_inputs` not found
```

so the HIR visitor could not be regenerated — the same shape as the codec
generator's `facet_abi.spl` reference and the dangling `flat_pool_debug_state_v1`
call (#4230). **Four** functions had been dropped from
`src/app/compiler_schema/fold_gen.spl` while `main.spl:17,54,68` kept importing
them:

| function | recovered from |
|---|---|
| `fold_inputs_valid` | `9bb344bb1cf` |
| `prepare_fold_inputs` | `9bb344bb1cf` |
| `generate_folds_prepared` | `9bb344bb1cf` |
| `fold_variant_report_prepared` | `9bb344bb1cf` |

`9bb344bb1cf` is an ancestor of `release/1.0.0`; the functions were lost by the
merge resolutions `545eb542c2b` / `e5b290e42a0`, not deliberately deleted.
`origin/main` is identically broken. They are restored verbatim, and both
subcommands now exit 0.

Regenerating with them produced a 3-line refresh of the generated visitors (two
diagnostic strings the stale output lacked, plus `registry-hash` 597583032 ->
931883717), confirming the generated artifacts had drifted while the generator
was unrunnable.

## Pattern

This is the fourth instance of one class on this branch: a reference kept while
its definition was lost in a merge resolution.

| instance | shape |
|---|---|
| `src/lib/common/facet_abi.spl` | declaration source referenced, file never tracked in git |
| `flat_pool_debug_state_v1` | call landed, definition never merged (resolved by #4230, deleting the call) |
| `codec_gen.spl` parity | generator older than its own output |
| `fold_gen.spl` x4 | functions dropped, importers kept |

All are consistent with the stale-snapshot rewind class that
`.claude/rules/vcs.md` already names (`push-no-stale-snapshot-rewind`,
`e274cd33719`). A regenerate-and-diff gate exists for the codec
(`push-hir-codec-complete`) but there is **no equivalent for the visitor/fold
generators**, which is why this one went unnoticed until a bootstrap needed it.
