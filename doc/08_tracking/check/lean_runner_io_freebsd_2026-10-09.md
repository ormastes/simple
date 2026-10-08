# Lean runner IO — focused cycle 1

Three real assertions passed on FreeBSD ARM64: exact generated source persistence; file-as-parent write failure with nil prover exit; missing configured executable with persisted source and failed result. Actual runner output: 3 passed, 0 failed, 230 ms, file PASS. Guard exit0, quiescent1, peak441672 KiB, compiler RSS cap5859375 KiB, deadline150s; inner test120s.

Runner source SHA256 b3ccbe23eb2b7a14215627df0b387f13fd958f8a546ebca272e8cad8c3a7c93b matches the independent static review and guest. Six frozen source hashes match the guest; see source-identity.json and guest-source.sha256. Producer SHA256 daadf4c854c0ef8d5a0d9cf33379c3dd28a1f7ba7c93a6b915c77973943fb721; explicit interpreter execution.

Limits: test output warns of duplicate process/pipe/sha classes from candidate and producer e934 checkouts. This qualifies the observed IO assertions, not a pure-source closure or release. No actual Lean proof or Lake build was executed; Lean is absent. Skip-accounting remains blocked by the separately recorded resolver defect. Coverage80% is a declaration, not measured evidence. No passing criterion rerun.

## Remaining gates

- Correct the separate member-import resolver defect before skip-accounting and genuine Lean E2E admission.
- Actual Lean proof acceptance/rejection requires a compatible native FreeBSD Lean installation; unavailable in this VM.
- Lake child cwd/toolchain behavior is statically reviewed, not runtime validated.
- Mixed-source dependency resolution must be reconciled before production or release qualification.
- Publisher verification and release controls remain outstanding.

Raw logs, guard receipt, launch script and exact source identities are retained in the owning worktree `build/runner-io-validation/`; no full-suite result is asserted.
