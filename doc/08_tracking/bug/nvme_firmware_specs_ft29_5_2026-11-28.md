# NVMe firmware specs: missing FsblVector struct and examples watchdog (ft29-5)

Status: verification-pending

## 1. nvme_cosmos_openssd_boot_spec
Symptom: child dies by signal; semantic error at :110:25, undefined `FsblVector`.
Root cause: commit 25a28ec0a5a ("isolate Pure Simple FSBL decisions") moved the
vectors to a TSV and deleted `struct FsblVector` from the spec, but the TSV
loader still constructs `FsblVector(...)`. The struct was never re-added (not an
import or rename issue). Fix: restore the struct in the spec.

## 2. nvme_base_spec_commands_spec (1/2)
Symptom: "expected 1 to equal 0" on the controller lifecycle scenario.
Root cause: `simple run examples/.../nvme_main.spl` passes every check but takes
~27 s interpreted; the seed's examples watchdog
(`examples_safety.rs`, default 10 s) kills it during step [10]
(checkpoint + power-fail + recovery), exit 1. With SIMPLE_TIMEOUT_SECONDS=300 it
prints ALL NVME CONTROLLER E2E CHECKS PASS, exit 0. Fix: `_run_simple` exports
SIMPLE_TIMEOUT_SECONDS (default 120), same precedent as
nvme_firmware_simulation_spec.spl.

Open perf item: step [10] interpreted cost (checkpoint/power_cycle) is the bulk of
27 s; not investigated here.

## Tests
Repro: the two specs themselves (failed before). Prevention:
test/03_system/app/nvme_firmware/nvme_spec_harness_prevention_spec.spl.

## Verification caveat
The seed in C:/dev/simple cannot run the test runner against origin/release/1.0.0
sources (`unknown decorator @representation_boundary`), so fixes were verified by
direct `run` of the example, the exact shell command, and a struct+call probe.
