# Full implementation progress

Source base: c5f33e7b09392200b36b44876aadfac9e5ade251, remote release_phase3. Isolated workspace: /home/ormastes/simple-dbc-plan-landing-20261012; branch work/dbc-full-implementation-20261012. Shared release worktree dirty source is other-session work and excluded.

| Feature | Current authoritative evidence | Remaining |
|---|---|---|
| F01 contracts | New common/contracts/distributed_control_v2.spl defines value envelopes, exact environment matcher and scoped grant authorization; negative unit scenarios authored | Runtime checks, versioned wire codec, caller wiring and actual activation |
| F02–F16 | Design and plan retained; full scope selected | Implementation, owner integration and real runtime/provider acceptance |

## M0 runtime inventory

Neither main shared workspace nor release_phase3 shared workspace has bin/simple or bin/release. bin/simple-interp searches only those deployed paths and fails closed. Candidate binaries found under bootstrap/diagnostic trees have not been admitted for general test/SPipe use. No Rust seed or unqualified Phase 3 substitution is permitted. Remote cross-host/platform/provider evidence has not been collected.

New tests: test/01_unit/lib/common/contracts/distributed_control_v2_spec.spl. Execution NOT_RUN; coverage not claimed. Source contracts are not authentication, durable command admission, a sandbox or a working remote tool. No feature completion or Phase 3 PASS is claimed.

Next: locate or build an admitted pure-Simple self-hosted runtime under bootstrap owner rules; run focused contract tests once, then connect shared facets and existing Caret/build owners with real integrated SPipe scenarios. Numerical routing/performance NFRs remain proposed pending measured baseline; semantic no-fallback requirements are selected.

## M1 composition increment

Source: src/app/llm_caret/workbench/distributed_composition.spl. Seven closed descriptors cover HostAuthority, Session, Build, Artifact, EvidenceCI, SourceLifecycle and Client. Facet IDs share KpfId128 namespace 0x4442435632 and are declared once; all consumers require explicit facets. Existing mdsocpp_seal_v1 owns graph/capability/memory/concurrency validation. Capacities are caller supplied; descriptor construction is not runtime reservation, activation, provider execution or proof of no-GC hot-path behavior.

Tests: test/01_unit/app/llm_caret/distributed_composition_spec.spl adds four positive/rejection scenarios. Execution NOT_RUN. Runtime path rechecked this continuation: deployed bin/simple and bin/release/x86_64-unknown-linux-gnu/simple remain absent. Remote release_phase3 remains c5f33e7b0. Next source work: canonical versioned codec and existing-owner admission wiring, with bounded transport and durable operation receipts.
