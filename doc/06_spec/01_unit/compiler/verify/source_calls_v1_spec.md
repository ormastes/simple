# Source-call inventory

Requirement: REQ-FV2-C1. Executable specification:
`test/01_unit/compiler/verify/source_calls_v1_spec.spl`.

Status: **12 scenarios authored; all UNRUN**. This is a manually maintained
companion. Qualified SPipe execution, generated-manual maintenance, compilation,
and coverage measurement remain pending. No formal verification result is
asserted by this manual.

Run the public command with a self-contained source module and explicit target:
`simple gen-lean source-calls FILE.spl x86_64-unknown-linux-gnu`.
Success means the compiler completed call capture and manifest finalization.
The report always states `formal_status=NOT_CHECKED`.

| Scenario | Action | Required observation |
|---|---|---|
| Real direct call | Parse a declared `leaf` and `caller`, lower HIR, capture the call | Exactly one binding; the actual manifest validator closes; source digest and target agree; report contains the exact manifest hash and unchecked status |
| No calls | Lower one leaf function for explicit aarch64 Linux | Zero bindings and a nonempty resolver receipt; frontend retains aarch64 |
| Malformed parser input | Supply an incomplete function parameter list | Parser error; no inventory result |
| Unresolved HIR call | Call an undeclared function | HIR error; no inventory result |
| Invalid target | Supply empty, host, native, malformed, ambiguous-OS, or newline-injected target | Target error before malformed source is parsed |
| Imports | Supply an external import | Unavailable driver-graph error |
| Source AOP advice | Parse actual `on pc{...} use ... before` syntax | Unexecuted-transform error |
| Retained DI declaration | Add the real `DiBinding` record to an actual parsed module and invoke the production boundary | Unexecuted-transform error; this scenario does not claim DI source-grammar coverage |
| Source mutation | Add a source comment and parse again | Different source digest; new cfg receipt retains the new digest |
| Wrong arity | Supply zero, one, or three command arguments | Usage error before file access |
| Missing file | Request a nonexistent regular source path | File error, no inventory |
| Directory | Pass the source directory as the input file | File error, no inventory |

The scenarios use the real frontend, HIR lowering, MIR capture producer and
manifest validator. They do not launch Lean, a proof checker, replay,
native compilation, or a release gate. C1 transformed-source provenance,
C6 authenticated checking/replay and C7 refinement remain open.
