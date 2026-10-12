# Distributed control verification runtime unavailable

Status: OPEN. Owner: distributed-control implementation / self-hosted runtime admission owner. Scope: verification and landing, not proof of a language defect.

Observed 2026-10-12: shared /home/ormastes/dev/simple and /home/ormastes/simple-caret-release-phase3 have no bin/simple or bin/release runtime. bin/simple-interp:14–18 routes exclusively to these deployed candidates. Candidate bootstrap binaries lack verified general SPipe admission for this lane.

Existing full-CLI receipts under build/standalone/caret-recovery/full-cli report attempts 1, 2 and 3 TIMEOUT, no output binary (120/600/1800 seconds). These are prior-owner receipts, not this lane's reruns. Process inspection on this continuation found no live native-build/caret-recovery full-CLI process; no verified wait exists.

Impact: contract, codec, composition and admission specs are authored but NOT_RUN. No branch coverage, runtime PASS, general Phase 3 qualification or implementation landing may be claimed.

Unblock: admit a pure-Simple runtime with full CLI/test/SPipe closure and retained exact binary/source/provider lineage; run focused specs once against this source, generate current manuals, complete required dependency checks and review before landing. Do not substitute Rust seed or diagnostic Phase 3 binary.

## User-directed runtime repair

User requested fixing the missing runtime on 2026-10-12. Owner claimed by current Codex lane. Exact reproducer: /home/ormastes/simple-caret-release-phase3/bin/simple-interp test test/01_unit/lib/common/contracts/distributed_control_v2_spec.spl --mode=interpreter, exit 127, no runtime found.

Canonical planner recovery uses admitted Stage 2 at /home/ormastes/simple-linux-bootstrap-build-20261009/logic-candidate-v4/stage2/x86_64-unknown-linux-gnu/simple. Initial request required explicit external output allowlist. With that supplied, actual planner compilation reported SCV-E-ADMISSION compile-event-journal-missing and prescribed SIMPLE_SCV_INVENTORY_COLD_INIT=1 for first build. Initialized through that supported cold path; no admission/no-stub checks disabled. Retained logs in build/runtime-recovery. Planner build session 86464 is live with compiler PID 123318 observed (86% CPU, ~115 MiB RSS at observation). This is recovery progress, not runtime admission or test PASS.

## Subsequent canonical recovery evidence

The preceding planner/process observation is historical. Planner compilation subsequently succeeded, but the old lineage could not resume general qualification because its compiler-test PASS receipt was unavailable. Fresh canonical bootstrap was selected instead. Mounted source/output initially failed exact immutable artifact modes after successful Rust compilation. Native source and authority output now reside under `/mnt/wsl`; only bulk mutable storage and the retained Cargo cache use the mounted drive. No mode/admission checks were weakened.

Latest frozen source is b36501e87 in `/mnt/wsl/simple-dbc-native-recovery-20261012`; output `/mnt/wsl/simple-dbc-native-bootstrap-20261012`. Recovery master log `/mnt/c/Temp/dbc-native-authority-stage2-20261012.log` records successful Rust package builds, successful immutable authority publication, bootstrap preflight PASS (5 checks, zero failed/skipped), and the start of Stage 2 compilation of `bootstrap_main.spl`. This proves recovery advanced past the prior filesystem failure, not Stage 2 admission, general CLI/test-runner qualification or feature test PASS. Feature increments after the frozen source remain separate and are retained in Git bundles on the mounted drive.

## Stage 2 admission and pending compiler matrix

The next attempt corrected preflight to measure actual Cargo storage and restored a checkout-owned native build directory (source 6b1978ce6). It reused 1,235 modules, rebuilt two, passed both frontend modes and receiver/runtime sanity, and published `stage3/x86_64-unknown-linux-gnu/stage2-admitted/admission.env` with status admitted. Candidate digest: `041e685fdbb0bb24eeec571a28d8bea57537909cd642116372bf4a8407fce1c8`. Its immutable runtime capsule was also published. Master log: `/mnt/c/Temp/dbc-native-owned-snapshot-stage2-20261012.log`.

Bootstrap then stopped before compiler tests ran: delegated-seed rows require explicit MC/DC-off waiver metadata. No waiver was invented. The supported `BOOTSTRAP_STAGE2_TEST_DELEGATE=0` path now runs the phase matrix using this admitted candidate, with normal strategy, slim profile, four build threads, two test workers and the unchanged 3,600-second work timeout. Log: `/mnt/c/Temp/dbc-stage2-native-matrix-20261012.log`. Matrix result and general CLI/test-runner qualification remain pending. This Stage 2 admission is not Phase 3 PASS or distributed feature verification.
