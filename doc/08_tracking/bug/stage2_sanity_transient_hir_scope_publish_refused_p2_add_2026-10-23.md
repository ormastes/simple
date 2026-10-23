# Stage 2 sanity rejects its own candidate: `transient HIR scope end failed` on `p2_add.spl`

- **Date:** 2026-10-23
- **Status:** OPEN — reproducible in 97 ms; failing sub-step not yet isolated
- **Lane:** `release/1.0.0`, Linux x86_64, `--backend=cranelift`
- **Blocks:** Stage 2 admission, and therefore Stage 3, Stage 4, the Stage 3
  planner receipt, and any full bootstrap on this branch

## Symptom

`bootstrap-from-scratch.sh --strategy=adhoc --backend=cranelift
--full-bootstrap --stop-after-stage2` builds the Stage 2 candidate, then its
own sanity gate rejects it:

```
[ERROR] phase 3 FAILED
[ERROR]   transient HIR scope end failed for .../src/compiler/bootstrap_admission/p2_add.spl
[hir-shard] owner=0/1@0 status=BLOCKED exit=1 claimed=1 sealed=1 finished=false
error: HIR aggregate failure; final worker and artifact publication blocked
candidate_frontend_smoke: p2_add-build failed (raw rc=1)
error: Stage 2 bootstrap compiler sanity failed
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

The rejected binary is preserved at
`.simple/storage/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple.rejected`.

## Reproduction — 97 ms, no bootstrap required

This is the useful part of this record. The whole failure reproduces directly
against the preserved candidate, so nobody needs to spend ~40 minutes on a
bootstrap to iterate:

```sh
R=.simple/storage/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple.rejected
CAP_MEM_MAX=4G sh scripts/resource/run_capped.shs \
  "$R" native-build src/compiler/bootstrap_admission/p2_add.spl -o /tmp/p2_add
# rc=1, fails at elapsed_ms=97:
#   error: in-process native-build: transient HIR scope end failed for
#          src/compiler/bootstrap_admission/p2_add.spl
```

`p2_add.spl` is a 23-line fixture (bool/text/`[i64]`/`[text]` tag functions and
an `if` chain). Nothing in it is exotic — no interpolation, no dict literals, no
nested generics.

`SIMPLE_NSCOPE_HIR_TRACE=1` narrows it to the step after promotion:

```
[nscope-hir] aliases-enter path=.../p2_add.spl content_len=487 module=compiler.bootstrap_admission.p2_add
[nscope-hir] retained-enter path=.../p2_add.spl entry=true
[nscope-hir] retained-pre-lower
[nscope-hir] retained-lowered
[nscope-hir] retained-paused
[nscope-hir] retained-promoted          <-- last successful step
[ERROR] transient HIR scope end failed
```

So lowering, the pause, and every ownership promotion succeed. The refusal is in
`driver_publish_reverse_reference_parse_scope_v1`, called at
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:581`.

## One message, three causes — why this is hard to triage

`driver_publish_reverse_reference_parse_scope_v1`
(`src/compiler/80.driver/driver_hir_pipeline_support.spl:72`) returns `false`
from **three** distinct steps:

| step | call | returns false when |
|---|---|---|
| 1 | `reverse_reference_module_seal_v1(token)` | nil/mismatched/already-sealed/invalid batch, or `transient_promote` fails |
| 2 | `driver_end_transient_parse_scope()` | `_sffi_transient_array_scope_end()` → `rt_transient_array_scope_end()` returns 0 |
| 3 | `reverse_reference_module_publish_v1(token)` | publication refused |

All four of its call sites collapse those three into a single message
(`driver_hir_pipeline_lowering.spl:583`, `:666`, `:979`;
`driver_hir_pipeline_support.spl:99`), and none names the step. Note the
contrast: **every sibling failure branch above line 581 names its own cause**
("HIR diagnostic ownership promotion failed", "HIR phase memo ownership
promotion failed", "HIR symbol table ownership promotion failed", "flat HIR row
ownership promotion failed", "frontend registry promotion failed"). Only this
one is ambiguous, and that ambiguity is what makes the defect expensive to
locate. Splitting it into three distinct reasons is the recommended first
change — it costs one rebuild and permanently removes this triage step.

## Hypotheses already ruled out (do not redo these)

- **Not the known entry-closure instance.**
  `doc/08_tracking/bug/entry_closure_seed_transient_hir_scope_end_failed_2026-10-20.md`
  records this exact message as FIXED, root-caused to
  `reverse_reference_module_seal_v1` losing a mutation through `unwrap()` copy
  semantics. That fix **is present** on `release/1.0.0`
  (`src/compiler/00.common/cache/reverse_reference_facts.spl:101` stores the
  mutated batch back at `:113` via `_reverse_reference_module_batch_v1 = Some(batch)`),
  and its spec `test/01_unit/compiler/80.driver/reverse_reference_batch_writeback_spec.spl`
  is in the tree. The symptom recurs with the fix in place, so this is a
  different cause wearing the same message. That doc's claim is correct for its
  own case and is not superseded.
- **Not `pause` deactivating the scope.** A plausible reading is that the
  retained path pauses the scope and then cannot end it. It is wrong:
  `rt_transient_array_scope_pause` (`src/runtime/runtime_native.c:1835`) sets
  `rt_core_transient_array_scope_paused = 1` and leaves
  `rt_core_transient_array_scope_active` at 1, so
  `rt_transient_array_scope_end` (`:1846`) still passes its `active` check.

## Remaining candidates for step 2

`rt_transient_array_scope_end` returns 0 on exactly three conditions:
scope not active (ruled out above), **owner-thread token mismatch**
(`rt_core_transient_scope_owner != &rt_core_transient_scope_thread_token` —
worth attention because the failure is reported by a `[hir-shard] owner=0/1@0`
worker), or `rt_transient_raw_scope_end()` failing under
`SIMPLE_RUNTIME_MEMORY_OWNER` (implemented in the Rust runtime, not the C one).
None of the three emits a diagnostic.

## Suggested order of work

1. Split the three reasons in `driver_publish_reverse_reference_parse_scope_v1`
   and propagate them into the four call-site messages.
2. Rebuild Stage 2 (`--full-bootstrap --stop-after-stage2`; the Rust seed is
   cached, so this is the short path) and read which step the new message names.
3. Fix that step, then re-run the same 97 ms reproduction before any bootstrap.

## Host note

This host has no LLVM 23 (only 16/18), so the lane ran `--backend=cranelift`,
which is admitted under the canonical K1 policy
(`scripts/bootstrap/bootstrap-from-scratch.sh:861`). Whether the failure also
occurs under the llvm backend is **not** established here and should not be
assumed either way.
