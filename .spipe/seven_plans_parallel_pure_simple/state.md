# Seven plans: parallel pure-Simple implementation

## Raw Request

Complete the seven items on Windows and WSL in parallel; implement in pure
Simple and use TDD with the SPipe skills.

## Task Type

feature

## Refined Goal

Complete the retained seven-plan requirements with pure-Simple implementation,
real regression scenarios, and separate Windows and WSL qualification evidence.

## Acceptance Criteria

- AC-1: Every retained requirement in the canonical seven-plan umbrella maps to
  its production owner, executable test, and outstanding host evidence.
- AC-2: Each bug fix records an observed pre-fix failure, the exact regression,
  and a meaningful adjacent case before its implementation is accepted.
- AC-3: Feature logic is implemented in `.spl`; native compilation uses Clang
  23.1 / clang-cl, without GCC or cl.exe substitution.
- AC-4: Focused checks report actual executed counts and failure status; Phase 1
  diagnostics never count as admitted SPipe, native-host, or release proof.
- AC-5: Changed scenarios have reviewed SPipe manuals and requirement links;
  missing admitted docgen/test runtime remains an explicit blocker.
- AC-6: Windows and WSL requirements pass separately on admitted pure-Simple
  tooling before either host is marked complete. Existing three-cycle caps
  remain in force; an unchanged green check is not repeated.
- AC-7: Update affected design/plan evidence, developer guides, feature/layer
  expert knowledge, and bug records in each lane. Record unaffected artifacts
  as N/A with a reason. Keep blocked criteria and their resume actions visible.
- AC-8: Integrate only owned files, review the exact resulting diff, and publish
  through a PR. An implementation handoff does not close umbrella verification.

## Cooperative Review

Parent `/root` owns integration, final review, host qualification, and the
umbrella status. Three same-model agents own disjoint changes:

| Agent | Plans | Approved source ownership |
|---|---|---|
| items_2_6 | 2 and 6 audit; item 2 implementation | new `src/lib/scv/distributed_identity_map.spl` and matching unit spec |
| items_3_7 | 3 and 7 | `src/app/optimize/collection_plan_cli.spl` and matching unit spec |
| items_4_5 | 4 and 5 | `src/lib/nogc_async_mut/link_working_set/spill.spl` and associated planner spec |

Each agent may write uniquely named bug/evidence documents. Parent stages and
commits; agents do not incorporate unrelated changes. No shared helper API is
introduced between these independent lanes. Each scenario uses imperative
`step("...")` descriptions and real production calls; no no-op checker or
placeholder passing assertion is permitted. Lower-model sidecars are N/A:
these agents use the inherited model. Parent reviews manuals and done marks.

## Phase

implementation-in-progress

## Evidence Limits

At resumption no plan is certified complete on Windows or WSL. Windows SDK is
installed, but clang-cl still lacks Visual C++ runtime headers after installer
exit 1602. The checked WSL workspaces have no deployed Stage 4 runtime; the
previous bootstrap stopped at the compiler-test admission gate. Earlier
runtime-compiler diagnostics exhausted their three-cycle limit with 10/12
passing. They are not automatically rerun by this parallel task.

Existing tracking IDs and canonical task registration must be reconciled using
the admitted tracker; this file does not invent task IDs or claim a database
registration that has not executed.
