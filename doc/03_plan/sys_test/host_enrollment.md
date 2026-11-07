# Enrollment verification handoff

Status: **AWAITING_VERIFICATION**. Finish the scoped tests below before evaluating the larger local host path. No build or test execution has been performed for this source slice, and no build slot is assigned. Every verification/check/build process must inherit `taskset -c 0-4`; all campaign lanes share this CPU set, limiting aggregate work to five cores. Obtain root allocation before a build.

## Executable inventory

- `test/03_system/app/orchestrator/feature/host_enrollment_spec.spl`: six authored cases for canonical complete binding, real dual-role signatures, all binding mutations, local scope/context/expiry, forged rebinding and malformed/oversize inputs. Fixture: `test/fixtures/orchestration/host_enrollment_native_probe.spl`.
- `test/03_system/app/orchestrator/feature/host_enrollment_claim_spec.spl`: five authored cases for real private-root publication/readback, native-slot duplicate rejection, signature/expiry rejection before mutation, final publication-time expiry, retained pending/unknown records, and unsafe configuration refusal. Fixture: `test/fixtures/orchestration/host_enrollment_claim_fixture_v1.spl`. Cases group related assertions; count is not runtime evidence.
- Authored manuals mirror both specs under `doc/06_spec/03_system/app/orchestrator/feature/`. They are not generated execution reports.

Run both specs with an explicitly identified admitted runtime. Record runtime path/hash/provenance, exact commands, actual executed case counts and artifacts. Then run the required compiler/library/MCP/LSP checks and MCP stdio integration gate for library changes, followed by the appropriate full suite under the same CPU budget. Do not substitute Rust seed or reuse an unadmitted build result as qualification. No previous passing checks should be repeated without changed evidence.

## Unverified failure paths

Post-claim mode/temporary-directory creation failures, individual object write/readback failures, changed pending records during publication, final claim write failure and lock-release failure have defensive source paths but no fault-injected runtime evidence. A crash after private-root creation and before its path is retained can leave an orphan private directory; its machine claim remains held. No cleanup scan, automatic adoption or absence inference is permitted. Add meaningful owner-level fault testing if the verifier requires it; do not install fake passing failure hooks.

## Larger acceptance remains separate

Native observations in this fixture are explicitly synthetic caller inputs. Signed authorization approves the binding but does not observe machine/provider identity. The public host-local-init/prepare/execute/inspect commands, installed-parent acquisition, provider identity/execution routing, durable execution observations, reconciliation and terminal/remote composition remain unimplemented in this slice. Full-system acceptance still requires actual submitted work, independent native identity/output inspection, capacity accounting and no replayed effect after restart. A source review or constructor/codec test cannot satisfy that gate.
