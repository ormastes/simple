# Mission-Critical Infrastructure Hardening V2 Feature Expert

## Role

Own the cross-cutting release contract that hardens the production Simple
toolchain, SimpleOS, rendering stack, bounded process execution, and the
versioned relaxed-allocation profile. Keep policy-model, controlled-contract,
live-host, and release evidence visibly distinct.

## Authoritative Links

- SPipe state: `.spipe/mission_critical_infra_hardening_v2/state.md`
- Selected requirements:
  `doc/02_requirements/feature/mission_critical_infra_hardening_v2.md` and
  `doc/02_requirements/nfr/mission_critical_infra_hardening_v2.md`
- Architecture/design:
  `doc/04_architecture/mission_critical_infra_hardening_v2.md` and
  `doc/05_design/mission_critical_infra_hardening_v2.md`
- Executable classification:
  `test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl`
- Operator plan and release chain:
  `doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`,
  `scripts/check/check-mci-v2-release.shs`, and
  `scripts/check/check-mci-v2-aggregate.shs`
- Full SimpleOS umbrella:
  `scripts/check/check-simpleos-hardening-evidence-matrix.shs`

## Non-Negotiable Invariants

1. `RelaxedAllocationProfileV1` is bounded, sealed, per-domain, and forbidden
   in declared critical contexts; strict allocation remains the default.
2. Controlled fixtures and policy models never become live or release PASS.
3. Every live lane emits content-addressed evidence, receives external signing,
   and is admitted by the common aggregate root before independent review.
4. Missing hardware, cross-host, 24-hour, docgen, or pure-Simple compiler
   evidence stays `blocked`; cached reports and timestamps cannot replace it.
5. Process ownership uses the canonical facade/ABI, bounded capture, exact
   process-group identity, and registered reap; every signal/wait path rejects
   `pid <= 0`.
6. Rendering claims require real backend provenance and device-origin evidence;
   CPU mirrors, screenshots, or synthetic handles are diagnostics only.

## Current Release Boundary

The 51-scenario classification is broader than release achievement. Read each
row's `class`, owner, reason, and resume fields before acting. In particular,
compiler cross-host/negative-campaign rows and docgen provenance rows remain
blocked until their named prerequisites produce fresh receipts. The deployed
`bin/simple` must be checked for the bootstrap-seed warning before it is used;
the Rust seed cannot provide self-hosted SPipe or release evidence.

The canonical release order is: producers -> independent lane signer -> first
aggregate/candidate graph -> independently signed reviewer generation -> final
aggregate. A producer contract PASS proves its boundary only, not the release.

## Related Layer Experts

- `doc/00_llm_process/layer_expert/compiler_driver/skill.md`
- `doc/00_llm_process/layer_expert/mission_critical_memory/skill.md`
- `doc/00_llm_process/layer_expert/ui_render/skill.md`

## Update Rule

Refresh this entry whenever selected requirements, scenario classification,
producer schemas, signing/reviewer flow, aggregate policy, or blocked resume
commands change. Never replace an explicit blocker with capability prose.
