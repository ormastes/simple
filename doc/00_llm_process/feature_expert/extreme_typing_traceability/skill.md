# Extreme typing and traceability feature expert

Status: design handoff, 2026-11-01; no feature/runtime qualification.

2026-11-02 source candidate: the retained HIR typecheck consumer now projects
owned signature facts from live HM substitutions through
`compiler.types.type_infer.api_signature_projection_v1`, using
`compiler.common.api_signature_facts_v1` records and bounded CompileContext
storage. This adds a `src/compiler/30.types` owner route; it does not establish
effective exports, complete E1, fatal enforcement or engine parity. Archive
leases keep collection absent. Read the [current slice status and
bounds](../../../05_design/extreme_typing_traceability.md#e1-retained-signature-observation-candidate-2026-11-02)
before extending the source. Authored projection/lifetime/storage specs are
unrun pending an admitted runtime; no generated manual or proof is claimed.

Read the [selected policy](../../../02_requirements/feature/extreme_typing_traceability.md),
[architecture](../../../04_architecture/extreme_typing_traceability.md),
[implementation plan](../../../03_plan/agent_tasks/extreme_typing_traceability.md)
and [acceptance plan](../../../03_plan/sys_test/extreme_typing_traceability.md).
The existing [traceability roadmap](../../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md)
retains its selected 20 requirements and 40 criteria.

Robust+ public Simple APIs may expose no bare true builtin primitives, including
bool/text/char; public generics require domain-safe bounds. Easy nominal
construction is required. Private representation is legal; public raw
constructors/getters/conversions, allowlists and private-FFI reexports cannot
bypass the rule. Compiler owns canonical types/effective visibility.

Extend common traceability and existing Slop; one projection supplies all
adapters. Caret owns session/worktree lifecycle. Keep definitions, observations
and qualified evidence distinct. Read-only overlap is not a merge conflict.
Open architecture options do not reopen the selected language policy.

Consume the exact feature/layer receipt before source work. New source routes,
manuals and implementation claims require revalidation; this expert note does
not activate proposed CLI commands or broaden operational skills.
