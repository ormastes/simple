# Interpreter cross-module local mutation clobber

Status: RED — claimed; minimal cross-module frame hypothesis did not reproduce.

Claim owner: Codex `/root/frame_sync_fix` (2026-08-11).

## Symptom

In `mission_critical_infra_hardening_v2_spec.spl`, a local
`DrawIrGenerationArenaV3` admits, seals, and successfully retires generation 1.
After calls into the domain-arena and bounded-process policy modules, the same
local object's `next_generation` is observed as `1`, not `2`.

Owner instrumentation proved, in order:

- SimpleOS validation passed.
- Draw IR admission/seal/retire assertions passed.
- DomainArena assertions passed.
- Process-policy assertions passed.
- Final state was `draw_next=1 domain_committed=0 domain_next=3 domain_high_water=64`.

The focused Draw IR owner spec performs the same terminal transition and
observes `next_generation == 2`. The defect therefore appears only after the
mutated local survives subsequent cross-module calls. This is consistent with
a stale caller/frame snapshot being restored over newer receiver state.

Changing `retire()` from an inline conditional to a standalone assignment did
not change the result, ruling out conditional-expression lowering as the owner.
The umbrella remained 2/3 with the same truth assertion failure.

## Durable evidence

- `build/native_probe/mission-critical-runner-startup/umbrella-owner-diagnostic.log`
- `build/native_probe/mission-critical-runner-startup/umbrella-owner-diagnostic.log.time`
- `build/native_probe/mission-critical-runner-startup/umbrella-after-fix.log`
- `build/native_probe/mission-critical-runner-startup/umbrella-after-fix.log.time`

Frozen seed executable SHA-256:
`df2da4952028ebbe3e89d0a2255d34c93e63522ad779d3444c5a0c82d3a0f5a0`.

## Required fix

Inspect interpreter call return/frame synchronization. A callee-refreshed
overlay must not overwrite newer caller-local or receiver state. Preserve the
mutation with its defining owner through foreign-module frames, then refresh
the matching caller.

Do not weaken or move the final invariant: it intentionally proves state
survives the complete cross-owner policy flow.

## Focused isolation result

The dedicated regression
`test/02_integration/compiler/interpreter/cross_module_local_mutation_clobber_spec.spl`
covers both of the initially suspected frame shapes:

- mutate a caller-local class receiver, call an unrelated imported function,
  then read the receiver again;
- mutate that receiver through a nested function in an imported module, then
  read it in the caller.

On the frozen bootstrap seed both pass (2 examples, 0 failures). This evidence
rules out ordinary imported-call frame restoration and ordinary nested imported
class mutation as sufficient causes. The pure interpreter already gives user
methods their own fast-local frame and restores `eval_current_decl_id` in
`_EvalOps/call_method_eval.spl`. No speculative evaluator change was made.

The remaining reproducer is therefore the complete DrawIR/domain/process
combination recorded above. Further isolation must preserve that combination
and bisect its calls or local-slot layout; a smaller test that does not fail is
not evidence that the umbrella invariant is repaired.

## Verification

After the interpreter owner is fixed and a fresh runtime is deployed, run the
umbrella once. Acceptance is exactly 3 examples, 0 failures, with
`draw_arena.next_generation == 2` after all cross-owner calls.
