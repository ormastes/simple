# Full SCV and phase 2 compiler: selected scope

Date: 2026-10-27. Status: requirements extracted from the user's supplied plans; implementation acceptance remains pending.

The user selected full SCV planning/design with phase 2 compiler integration, Astra guidance/review and smaller-model parallel work. This document indexes that selected direction. It adds no mandatory provider, numerical performance target, authority cutover, release publication, or implementation claim. The supplied [master plan](../../03_plan/app/tools/scv_sdn_solver_gateway_master_plan_2026-10-26.md) and [compiler plan](../../03_plan/app/tools/simple_scv_compiler_tldr_build_cache_implementation_plan_2026-10-27.md) remain the detailed requirement sources.

| Requirement | Selected behavior | Source | Planned acceptance |
|---|---|---|---|
| REQ-001 | SDN native configuration; schema checks and old-policy authorization | R01, R03; I05 | AT-C01–C05, AT-P01–P07 |
| REQ-002 | Separate source, DB schema/value, configuration and opaque solvers | R02–R04, R09 | AT-P04, AT-S01–S08, AT-D01–D08, AT-V01–V07 |
| REQ-003 | Preserve bytes and invalid private work across capture, solve and failure | R05, R07, R10 | AT-S06/S07, AT-E08, AT-O01–O09, AT-M01–M05 |
| REQ-004 | Stable source/DB identities and verified operations, with ambiguity retained | R08, R09, R11, R12 | AT-S01–S03, AT-E01–E05, AT-D01–D08, AT-I01–I08 |
| REQ-005 | Typed DB migration, field policies, cross-row constraints and causal retention | R02, R11, R12 | AT-D01–D08, AT-V01–V07, AT-I08 |
| REQ-006 | Hash purpose separation, algorithm tags, byte-safe structural storage/restore | R05, R06, R10 | AT-H01–H07, AT-O01–O09 |
| REQ-007 | Hybrid/offline native clients, real gateway, durable publication and one authority | R12–R15 | AT-G01–G09, AT-I03–I08, AT-M01–M05 |
| REQ-008 | Exact candidate evidence, isolated agents, shared scheduling/context | R16 | AT-R01–R04, AT-Q01/Q02 |
| REQ-009 | Frozen compiler input including acknowledged overlays and exact path policies | Compiler §§4–6 | SCV-CACHE-04–09, -27 |
| REQ-010 | Reuse requires exact requested-snapshot read-set receipt, including absence | Compiler §§6–7 | SCV-CACHE-01–07, -09, -24, -28 |
| REQ-011 | Compiler owns semantic facets; full outgoing manifests update transactionally | Compiler §§8–9 | SCV-CACHE-08–15, -25, -26 |
| REQ-012 | Cache owns artifact encoding; generation-qualified container resolution and pins | Compiler §§9–11 | SCV-CACHE-15–20, -23 |
| REQ-013 | Embedded and BuildRunner default SRC→OBJ; shared TaskRunner, separate test evidence | Compiler §§5, 12 | SCV-CACHE-01/02, -21/22, -25 |
| REQ-014 | Versioned adapters preserve legacy hashes/action formats, gates and rollback | R15; compiler §§3, 13 | AT-H07, AT-M01–M05, SCV-CACHE-17–20, -24 |

GXHash, learned retrieval, structural deltas, raw-digest deferral and native protected-ref authority retain the original plans' optional or separately gated status. H03 can satisfy its contract through truthful capability/refusal handling without enabling GXHash. Any additional requirement or numerical service target needs user selection; do not auto-select from alternatives.

The requested deliverable is planning/design. Executable SSpec, implementation, runtime verification and release are later phases, not silently completed by this document.
