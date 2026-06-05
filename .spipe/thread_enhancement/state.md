# Feature: thread_enhancement

## Raw Request
$sp_dev impl with spawn agent thread_enhancement_plan.md and test intensively.

## Task Type
feature

## Refined Goal
Implement the thread enhancement plan by delivering a pool-backed task-spawn slice with correctness tests, preserving OS-thread `thread_spawn`, and preparing independently owned follow-up lanes for green-thread and preemption work.

## Acceptance Criteria
- AC-1: `doc/03_plan/runtime/thread_enhancement_plan.md` remains the source plan and records current implementation evidence, owned lanes, and remaining tier gates.
- AC-2: A pool-backed task spawn API exists in Simple stdlib code without changing the explicit OS-thread `thread_spawn` API.
- AC-3: Thread pool waiting does not rely on millisecond sleep polling in the implemented path.
- AC-4: Channel full-buffer behavior has a regression test or explicit verification evidence showing no silent drop in the changed path.
- AC-5: Spawn-agent lane outputs identify runtime, stdlib, compiler/preemption, and verification responsibilities with concrete files and gates.
- AC-6: Focused thread/channel/spawn tests pass in at least interpreter mode; native or broader mode failures are recorded with exact commands and causes.
- AC-7: Intensive verification includes the SPipe doc layout guard, relevant thread/channel tests, and the cross-language performance harness or a documented reason it cannot complete.

## Scope Exclusions
- Full Tier 1 green-thread scheduler productionization is not required before the Tier 0 pool-backed spawn slice lands.
- Tier 2 growable stacks and compiler preemption are design-spike outputs unless the lower tiers are already complete.
- `thread_spawn` remains the low-level OS-thread primitive and is not replaced.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
