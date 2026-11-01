# Extreme typing and traceability feature expert

Status: design handoff, 2026-11-01; no feature/runtime qualification.

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
