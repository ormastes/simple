# release/1.0 Phase 3 acceptance ledger

Campaign: current 2026-10-23 continuation; owner: coordinating bootstrap session.
This ledger specifies gates, not executed results. No build/test was launched
while authoring it. `KNOWN` means observed metadata only; `RUNNING` is an
observation, not acceptance; `UNRUN` means no qualifying receipt was reviewed.
Only immutable, same-lineage evidence can change a gate to `PASS`.

Observed workspace: `/home/yoon/dev/simple`, branch `release/1.0`, HEAD
`b09f63cba8485dd2cf78e44dbed62ba458e46877`; unrelated dirty
`src/compiler_rust/runtime/build.rs` is excluded from ledger ownership.
Observed campaign source directory: `/tmp/release-1.0.0-continuation-20261023`.
Output `O=/tmp/phase3-release100-stage2-cranelift-20261023`; target
`T=aarch64-unknown-linux-gnu`; selected backend `cranelift`.
At the authoring observation, PID 1912273 ran `--full-bootstrap
--backend=cranelift --stop-after-stage2 --output=$O --jobs=2
--jobs-memory-policy=explicit-count --keep-going`; progress milestone was
`stage2`. PID existence is not a terminal result. Other concurrent output roots
are separate lanes and cannot supply this campaign's missing evidence.

| ID / criterion | Command, artifact or test evidence to retain | PASS condition | Current status |
|---|---|---|---|
| A1 Input identity | Frozen source directory; `git rev-parse HEAD`; before/after source manifests and git state; argv/environment policy; source overlays and hashes; `$O/bootstrap-preflight.env` and bindings | Actual source commit/tree, ordered roots, dirty patches/overlays, target, backend, ABI, host configuration and producer hashes are pinned; before/after identity agrees. Workspace HEAD alone does not identify the separate campaign source. | KNOWN paths/backend; identity gate UNRUN |
| A2 Seed/native prerequisites | `$O/rust-authority-*`, Rust authority fingerprint details, preflight logs; actual seed/runtime archives and headers; C compiler/linker/backend paths, hashes and versions | Required toolchain and native runtime resolve; seed/runtime match recorded inputs and target; native prerequisite checks succeed. Rust seed remains bootstrap-only; it cannot substitute for Stage2/3 behavior. | RUNNING campaign; prerequisite receipts UNRUN |
| A3 Stage2 self-hosted artifact | Existing Stage2-stop command above; `$O/stage2/$T/simple`; `$O/stage3/$T/stage2-admitted/admission.env`; Stage2 command transcript, runtime authority, sanity/receiver evidence and verification summary | Exact pure-Simple Stage2 is executable, identified by SHA-256, independently admitted, and passes its required probes and phase verification. A `.rejected` artifact or a link marker is not admitted. | RUNNING Stage2; no PASS reviewed |
| A4 Phase3 compiler | Canonical planner producer `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`; printed exact resume command `sh scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=$O --bootstrap-receipt=<bound-receipt> --stop-after-stage3`; `$O/stage3/$T/{simple,provenance.env,stage3-command.transcript}` and authority map | Typed reason targets `//bootstrap:stage3` and is explicitly selected from the producer allow-list; resume consumes this exact admitted Stage2/source/runtime. Stage3 build exits zero, natural link completes, provenance independently re-verifies against current hashes, rejection/frontend probes pass, and owned children are quiescent. | UNRUN; current command stops at Stage2 |
| A5 Real Hello, each producer | Stage2 and Stage3 sanity transcripts/receipts (`stage2-sanity.env`, `stage3-sanity.env`), fixture hash, full native-build argv, object/runtime/link inputs, executable hash, run stdout/stderr and exit | Each exact new compiler compiles and naturally links a real Hello fixture; its newly produced executable runs with exit 0 and the fixture's exact expected stdout. Compile/link/run exits and bytes are recorded separately. Stage2 Hello cannot qualify Stage3. | UNRUN |
| A6 Required tools and tests | `scripts/bootstrap/bootstrap-phase-verification.shs` with phase, compiler snapshot, source root and Stage3 provenance bound; phase-qualified full CLI, standalone runner and command-owner receipt; sorted test/build inventory, per-row logs/counts and terminal summary | Stage2 required matrix passes. Stage3 full CLI and runner are built by Stage3, with real dispatch, pinned child `SIMPLE_BINARY`, and receipt-bound MCP binary. Compiler-bootstrap, interpreter and loader cases execute; representative bootstrap/MCP cases cover interpreter and compile modes. Freeze every eligible `test/**/*_spec.spl` and `test/**/*_test.spl` via full-profile inventory: each required row terminal, positive executed count, zero failures/timeouts/crashes/discovery errors/unexpected skips; all required tool/module build rows pass. No empty/skipped-only success or missing `Results:` accepted. | UNRUN |
| A7 Cache correctness, if used | Producer/source/entry/target/backend/runtime/ABI/options fingerprints; isolated writable cache paths; reuse/invalidation receipts; `$O/stage3/$T/stage{2,3}-native-cache` and distinct phase/producer full-CLI/runner caches | Reuse has matching identities and dependency/layout keys; changed inputs invalidate affected entries; no parallel writers, cross-phase borrowing, restamping or copied PASS receipts. Alias use pins lexical/physical paths and staging ownership. If no reuse occurs, record that fact with build evidence before marking N/A. | UNRUN; cache gate not waived |
| A8 Resource/performance guard | Selected jobs receipt; process-tree RSS receipt beside native-build log; progress/events, elapsed/peak RSS, timeout policy, process-group ownership and terminal cleanup receipt; declared performance baseline/limits | Actual configured guards stay active and measurements complete within declared admission limits; no killed/orphaned children or unfinished archival. Record measured compile/link/run/test costs and any performance regression/bug. Diagnostic exceptions remain unadmitted until normal gates rerun. Report absent deadlines/baselines as gaps, not invented PASS. | KNOWN observed watcher: 2 jobs, enforced 13,631,488 KiB tree cap; outcome UNRUN |
| A9 Source changes / branch landing | Scoped diff and review; applicable regression evidence; `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` when landing source; zero executable specs under `doc/06_spec`; work-branch PR, reviewed exact head, comments/checks and merge SHA | All fixes used in the frozen candidate are mapped to owned commits/overlays and land through a reviewed PR into intended protected branch. Reconcile merged tree with candidate source fingerprint; requalify affected evidence on drift. Preserve unrelated dirty files. | UNRUN; no commit/push/merge performed by ledger task |
| A10 Protected remote admission | PR remote/base/head and merge receipt; branch protection/check/review evidence; frozen candidate/evidence manifest hashes and explicit campaign-owner admission receipt | Remote confirms intended source landing and authorized candidate admission after A1–A9; no direct protected-branch push, unresolved correctness finding, or genuinely failing introduced check bypassed. Local build success and remote source merge alone do not admit binaries. Release tags/publication require separate authorization. | UNRUN |

Required A6 matrix entries for this Linux lane are
`test/01_unit/compiler/bootstrap`, `test/01_unit/compiler/interpreter`,
`test/01_unit/compiler/loader/module_loader_relocation_spec.spl`, and
`test/02_integration/app/mcp_stdio_integration_spec.spl`. Retain both interpreter
and compile mode outcomes in the full Phase3 profile; Stage2's explicit slim
profile has its own required subset and cannot supply missing Phase3 rows.
Run through the phase-bound runner with `--assert-ran --no-cache --no-db
--no-session-daemon` and structured counts as the canonical verifier specifies.
These named cases supplement the frozen full inventory; they do not replace it.

Phase 3 **PASS** means A1–A10 are PASS for the same frozen source, Stage2
parent, Stage3 candidate hash, target and backend, with A7 N/A allowed only by
documented no-reuse evidence. All required inventory rows have terminal success,
positive executed tests and zero unresolved failures; the owner freezes a
hash-bound final admission receipt after reviewing the complete evidence.
Otherwise report `RUNNING`, `BUILT_NOT_ADMITTED`, `BLOCKED` or `FAIL`, naming
the first unmet gate. A diagnostic descendant may start after its producer's
Hello gate but remains unadmitted. This is the selected Cranelift/target campaign;
it grants no LLVM, Phase4, deployment, other-platform or publication claim.

Stage6 whole-repository release testing (`<qualified-full-cli> test test --whole
--mode=interpreter`) and platform handoff readiness are later distinct gates;
neither is silently asserted by Phase3 acceptance.

Progress report template (fill from retained evidence; do not rerun green checks):

```text
Observed at: <timestamp>; source/tree: <pin>; candidate/producer: <path + SHA>
Lane: <target/backend/output>; process: <PID/group/live or terminal>
Current gate: <A#>; state: <RUNNING/BUILT_NOT_ADMITTED/BLOCKED/FAIL/PASS>
Last new evidence: <log/receipt path + bounded observation + actual exit>
Tests: <executed/passed/failed/skipped + inventory remaining; unknown if absent>
Resources: <elapsed/peak RSS/guard limits>; repair cycles: <n/6>
Remaining acceptance gaps: <A# list>; next finite action: <action>
Landing/admission: <PR/merge/evidence receipt or UNRUN>
```

Authority: [bootstrap entrypoint](../../scripts/bootstrap/bootstrap-from-scratch.sh),
[failure collection](../07_guide/tooling/bootstrap_failure_collection.md),
[producer-bound verification](../07_guide/app/llm/bootstrap_parallel_handoff.md),
[native staging and terminal evidence](../07_guide/tooling/bootstrap_native_staging.md).
Keep existing `plan.md` and historical receipts unchanged. Verify once per
criterion; changed evidence justifies a retry, with at most six repair cycles.
