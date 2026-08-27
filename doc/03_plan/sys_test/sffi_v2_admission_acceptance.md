# System-test plan: SFFI v2 admission acceptance

| Requirement | Scenario | Initial state |
|---|---|---|
| REQ-SFFI-ACC-001 | valid exact artifact admits once | developing |
| REQ-SFFI-ACC-001 | unsigned and altered artifacts reject | developing |
| REQ-SFFI-ACC-003 | signer, ABI, receipt, null-contract rejection matrix | developing |
| REQ-SFFI-ACC-004 | receipt/category has stable no-secret result | developing |
| NFR-SFFI-ACC-001 | admitted typed call has no admission work | developing source + runtime gate |
| NFR-SFFI-ACC-003 | missing fixture is FAIL/BLOCKED, never pass | developing |

The canonical executable target is
`test/03_system/compiler/sffi_v2_admission_acceptance_spec.spl`; its manual
mirror is `doc/06_spec/03_system/compiler/sffi_v2_admission_acceptance_spec.md`.
Do not count source-only audit assertions as provider admission acceptance.
