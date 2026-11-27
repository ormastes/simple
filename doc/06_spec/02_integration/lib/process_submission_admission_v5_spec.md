# Submission deadline reservation controls

Executable: `test/02_integration/lib/process_submission_admission_v5_spec.spl`.
Simple/native-owner status: **NOT_RUN**. Only the standalone clock helper has a
scoped compile/run PASS, with both attempts and hashes recorded under
`doc/09_report/process_submission_admission_v5_clock_20261107/`.

| Requirement | Actual owner control authored |
|---|---|
| REQ-SUBMIT-EXPIRY-001 | Reserve before effects; pass an expired Unix deadline; require consumed NoChild state, reject replay with a later deadline, then confirm the exact reservation release. |
| REQ-SUBMIT-EXPIRY-002 | A missing deadline fails into consumed NoChild state while retaining release ownership. |
| REQ-SUBMIT-EXPIRY-003 | Native clock helper tests cover unknown/invalid clock and exact `now == expiry`; the live native fixture must prove no final child creation on refusal. |

The clock mechanism selfcheck is
`src/runtime/test/runtime_process_submission_admission_v5_selfcheck.c`.
It uses a test-only clock syscall substitute and makes no live process claim.
The authored Linux and Darwin `runtime_process_submission_admission_v5_*_selfcheck.c`
live fixtures cover actual no-child/child/reap boundaries; both remain NOT_RUN.
Post-create expiry must retain the actual child owner until observed reap;
source inspection or a failed initial receipt cannot substitute for that test.
