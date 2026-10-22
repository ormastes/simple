# Native HIR contract probe crashes in SHA-256 streaming

Status: OPEN; blocks current-source HIR contract evidence and landing.

The owned completion lane built `test/fixtures/compiler/nogc_hir_contract_probe.spl` with the admitted r17 focused diagnostic producer and exact stage2 runtime authority. Final authorized attempt 10 published `build/nogc-hardening/nogc_hir_contract_probe_v10` after 864.14 seconds, peak RSS 35,489,488 KiB. Its guarded execution exited 139. GDB identifies `lib.common.crypto.sha256.Sha256StreamV1.update`. Repeated frames alone do not establish recursion; the precise representation or memory defect remains undiagnosed.

Evidence: `build/nogc-hardening/hir-contract-build-10.log`, `hir-contract-run-10.log`, `hir-contract-gdb-10.log`, and `verification-cycle-ledger.json`. This binary predates the separately reviewed byte-write adapter repair; do not attribute its crash to that fix.

The earlier attempt 9 registry record/integer conversion was repaired before this build. Reaching a later crash is progress, not a passing HIR contract. The ten-attempt cap is exhausted; no attempt 11 or acceptance closure is recorded. Preserve the existing cache and binary for subsequent authorized diagnosis.
