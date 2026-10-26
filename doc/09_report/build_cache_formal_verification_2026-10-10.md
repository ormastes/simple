# Build/cache source verification report

**Formal status: NOT CHECKED. Production readiness: WARN / incomplete.**

The narrow service fix prevents a result for action B from publishing under
action A's lease, and prevents a stale foreign lease from rejecting the current
owner's entry. Shared source:
`src/lib/compiler_artifact_service/service.spl:artifact_service_complete_v1`.

## Executed source evidence

Root ran three sealed, source-loaded Phase 1 diagnostics through frozen C642.
All used the reviewed Windows Job collector with 30-second, 512-MiB working-set
and 1-MiB log caps. Eight actual service/hash modules were loaded from immutable
private closures; binary, source, controller and log identities were checked.

| Run | Observation | Exit | Peak RSS |
| --- | --- | --- | --- |
| Original c48 service | Wrong-action publication and stale-owner poisoning reproduced | 11 | 30,504 KiB |
| Minimal candidate | Eight behavior controls passed | 0 | 30,264 KiB |
| Bounded candidate | 192 completion inputs, 625 traces, 16 dead-owner retries, 512 symbolic cost cases | 0 | 30,352 KiB |

Original log SHA256:
`c10ffe616180c594904431e1ac32aa1482b1e81d3d593dbfb61e8fbb291dccdb`.
Candidate log SHA256:
`1e58e1f4552e44bbbb309aea842fab05cb6b7ce4151ca05aa6d5b7824cd090d3`.
Bounded log SHA256:
`40a66633d6bf969b3c2aadc71498f723a91a80e92108588d2f863f430ae5fbf3`.
All jobs were empty before receipt publication. The tested candidate's physical
SHA256 is `2fe37878db6fa5eedce7a16436425ee52e9dd92753b152da9f0a2728ba9b4c5b`.
Git newline normalization creates a new physical source identity at checkout;
it must not be silently treated as the same artifact hash.

Retained receipts, loaded source lists and requests:
`build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/formal/`.
These are bootstrap diagnostics, not admitted self-hosted, backend or shipped
artifact verification. Passing controls do not prove crash recovery.

## Executable model and formal engine

Canonical SPipe specs are under `test/00_formal_verification/compiler/`:
`build_cache_service_refinement_spec.spl`, `build_cache_parse_reuse_spec.spl`, and
`build_cache_bounded_model_spec.spl`. Their authored manuals mirror those paths
under `doc/06_spec`; SPipe/docgen admission is pending.

The bounded checker calls actual production service functions over 192 completion
inputs, every four-event trace in a five-event alphabet (625 traces), and 16
retries of a leased action that never completes. It also checks 512 bounded
symbolic cold/warm work configurations. The final third verification cycle
completed with every expected count and actual source-load pin verified. The
service lane has consumed its three-cycle cap; no green rerun is permitted.
The dead-owner fixed point confirms missing recovery, not successful liveness.

`src/verification/build_cache/src/BuildCache.lean` contains 23 manual theorem
roots and explicit axiom-print commands. `source_bindings.json` and
`refinement_map.json` bind exact c48 source/functions and state evidence limits.
The model has not been checked by Lean. The typed FV2 lattice must not be
promoted by file presence, a manually matching hash, examples, or a bootstrap
execution result.

The actual Simple paths are distinct: the legacy CLI imports
`verification.proofs.checker` and invokes `lean --run file`; the structured
`verification.lean.runner.LeanRunner` invokes `lean file` and distinguishes
missing-tool errors. `verification.toolchain.ToolchainInfo` probes Lean/Lake.
No alternate SMT backend was found in that scoped workflow. A proof file with
no executable main must use the structured checker/manual Lean path, and a
bounded outer process must enforce limits independently of legacy configuration.

Neither Windows nor the already-running Ubuntu environment exposed Lean/Lake.
Official v4.30.0 release metadata lists a 541,369,115-byte Windows tar.zst and
778,020,756-byte zip. Measured free disk was 6,441,791,488 bytes; active Phase 3
growth plus safety reserves total 6 GiB (6,442,450,944 bytes). Even compressed
archive storage exceeds the remaining budget before extraction. No package was
downloaded. The measured forecast is retained in `formal/toolchain_capacity.json`.

## Performance, recovery and open gates

Cold work separates source capture, enumeration, hashes/reads, authoritative
parse, TLDR decode, HIR/MIR, object/link, startup/scheduling and receipt work.
The actual cold HIR receipt batch hashes the inventory/builds its index once
per invocation; a per-target whole-tree regression requires caller-frequency
evidence. The separate 80030 diagnostic's 49.453-second, 105-module receipt gate
is an investigation lead with unproven producer/source binding.

Weighted work is not milliseconds. Warm no-parse/no-scan accounting assumes an
admitted unchanged generation and retained parse. It does not justify skipping
validation on timestamps. No universal 0.1-second cold-build claim is made.

Crash recovery remains open: see
`doc/08_tracking/bug/build_artifact_service_dead_owner_requeue_gap_2026-10-10.md`
and `doc/05_design/build_artifact_service_owner_recovery.md`. The existing service
has no reclaim/requeue API, and the inspected runner heartbeat helper is a stub.
Neither fact alone establishes that every current runner mode deadlocks.

Remaining gates include actual AST restore/lifetime replay, concurrent parser
singleflight and owner death, shared TLDR/build/test-runner ownership, the root's
eight production header/invalidation scenarios, paired timing/RSS, full mandatory
compiler/lib/MCP checks and independent formal/refinement evidence. There is no
release PASS or merged-PR claim.

## Separate parser acceptance request

`formal/parse_reuse_request.json` seals an unexecuted actual c48 frontend replay
against the existing read-only baseline projection, without another source copy.
It checks retained rich AST values after flat-pool reset, restore without a new
parse, corrupt-frame rejection/recovery, supplied generations A/B/A with exactly
two parses, and invalid-source rejection without successful cache publication.
It does not claim TLDR/HIR or test-runner integration. This previously untested
acceptance has a separate attempt ledger; service verification stays closed at
three cycles.

The bounded request has a 30-second, 512-MiB sampled working-set limit and a
1-MiB log cap. Compiler-import RSS is not measured. Its preflight requires the
3-GiB disk reserve plus a 64-MiB cache allowance; that allowance is a forecast,
not a proved disk bound. At sealing, free disk was 1,534,623,744 bytes, so launch
is blocked before consuming an attempt. No Lean installation is authorized by
this request. Actual engine proof and admitted SPipe execution remain pending.
