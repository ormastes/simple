# Distributed control verification runtime unavailable

Status: OPEN. Owner: distributed-control implementation / self-hosted runtime admission owner. Scope: verification and landing, not proof of a language defect.

Observed 2026-10-12: shared /home/ormastes/dev/simple and /home/ormastes/simple-caret-release-phase3 have no bin/simple or bin/release runtime. bin/simple-interp:14–18 routes exclusively to these deployed candidates. Candidate bootstrap binaries lack verified general SPipe admission for this lane.

Existing full-CLI receipts under build/standalone/caret-recovery/full-cli report attempts 1, 2 and 3 TIMEOUT, no output binary (120/600/1800 seconds). These are prior-owner receipts, not this lane's reruns. Process inspection on this continuation found no live native-build/caret-recovery full-CLI process; no verified wait exists.

Impact: contract, codec, composition and admission specs are authored but NOT_RUN. No branch coverage, runtime PASS, general Phase 3 qualification or implementation landing may be claimed.

Unblock: admit a pure-Simple runtime with full CLI/test/SPipe closure and retained exact binary/source/provider lineage; run focused specs once against this source, generate current manuals, complete required dependency checks and review before landing. Do not substitute Rust seed or diagnostic Phase 3 binary.

## User-directed runtime repair

User requested fixing the missing runtime on 2026-10-12. Owner claimed by current Codex lane. Exact reproducer: /home/ormastes/simple-caret-release-phase3/bin/simple-interp test test/01_unit/lib/common/contracts/distributed_control_v2_spec.spl --mode=interpreter, exit 127, no runtime found.

Canonical planner recovery uses admitted Stage 2 at /home/ormastes/simple-linux-bootstrap-build-20261009/logic-candidate-v4/stage2/x86_64-unknown-linux-gnu/simple. Initial request required explicit external output allowlist. With that supplied, actual planner compilation reported SCV-E-ADMISSION compile-event-journal-missing and prescribed SIMPLE_SCV_INVENTORY_COLD_INIT=1 for first build. Initialized through that supported cold path; no admission/no-stub checks disabled. Retained logs in build/runtime-recovery. Planner build session 86464 is live with compiler PID 123318 observed (86% CPU, ~115 MiB RSS at observation). This is recovery progress, not runtime admission or test PASS.
