# SStack State: simpleos-rv64-hosted-qemu

## User Request
> next task from the plan — simpleos_rv64_hosted_qemu (hosted scenario, preflight guest, SSH/HTTP probes, smoke lane)

## Task Type
feature

## Refined Goal
> Implement RISC-V RV64 hosted QEMU infrastructure models: hosted scenario with target registration, preflight guest entry with alive probes, SSH/HTTP probe contracts with smoke media attachment, and SMF smoke lane configuration with lane entry tracking.

## Acceptance Criteria
- [ ] AC-1: HostedScenario — scenario name, arch (rv64), machine type (virt), cpu model, memory size
- [ ] AC-2: TargetRegistration — target triple, is_hosted flag, boot mode (hosted/baremetal), kernel path
- [ ] AC-3: ScenarioConfig — combines scenario + registration, readiness check, config validation
- [ ] AC-4: PreflightEntry — guest entry point, keep-alive flag, timeout, probe count
- [ ] AC-5: GuestProbe — probe type (ssh/http/serial), host, port, expected response, pass/fail status
- [ ] AC-6: ProbeResult — probe ref, latency, success flag, error message, retry count
- [ ] AC-7: SmokeMedia — media type (disk/cdrom/virtio), image path, attached flag, mount point
- [ ] AC-8: HostedBoot — boot sequence with preflight + probes + media, overall status
- [ ] AC-9: SmokeLane — lane name, lane type (smf/native), entry list, pass/fail gate
- [ ] AC-10: Verification spec — 20 tests covering scenarios, registration, probes, media, lanes

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 4 plan tasks. Existing: qemu_runner.spl (5 parts), ssh_qemu_contract.spl, desktop_qemu_contract.spl.

### 5-implement
<pending>

### 7-verify
<pending>
