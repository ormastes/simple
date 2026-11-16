# Actual Windows enrollment proof before managed machine admission

Status: **AUTHORED_NOT_RUN**. The two remaining scenarios and this manual are
source only. SPipe, docgen and runtime/native campaigns were not run.

Source: `test/03_system/app/orchestrator/feature/windows_managed_host_claim_v1_spec.spl`.

| Requirement | Scenario | Actual assertion |
|---|---|---|
| REQ-WINDOWS-MANAGED-HOST-001 | A matching issuer carries an invalid approval signature | The real verification factory returns `APPROVAL_SIGNATURE_INVALID` before parsing the deliberately invalid provider policy. |
| REQ-WINDOWS-MANAGED-HOST-002 | A valid signed enrollment borrows protected native policy ownership | The snapshot contains the verified issuer, exact authority-policy digest, signed binding and positive provider generation; closing the actual native owners invalidates the copied proof. |

The first scenario opens an actual protected native policy, corrupts one
approval-signature byte, and checks the genuine verifier rejects it. The second
requires actual Docker observation during fixture setup, verifies a real signed
enrollment, captures its snapshot, closes the actual native owners, and checks
the borrowed proof can no longer refresh. Open outputs, partial-open cleanup
and failed closes are retained before assertions in an explicit native cleanup
slot. Only successful LIFO closes remove their entries.

Both require a disposable administrator-prepared Windows private parent at
`SIMPLE_WINDOWS_DEPLOYMENT_PRIVATE_PARENT`, actual private-file runtime support
and the real provider-policy fixture children. The fixture uses test-only real
signing keys. These proof tests do not establish the installed machine trust
pin or machine admission. No mocked provider, fabricated owner, skip or
conditional passing oracle supplies acceptance.

REQ-WINDOWS-MANAGED-HOST-003 positive fresh enrollment through local Host and
reopen is **BLOCKED / NOT_COVERED**. Its earlier authored positive oracle has
been removed after the actual migration-fence genesis safety gate made it
unreachable. The prior six-file frozen snapshot remains historical source,
not current supported admission behavior or passing evidence. Genuine
pre-existing-charge recovery has no qualifying external fixture here and is
also **NOT_COVERED**; manually seeded WAL rows cannot substitute.

The current fresh-enrollment refusal contract is authored separately in
`windows_host_migration_genesis_guard_v1_spec.md`. Conflicting scope admission,
aggregate capacity, execution mutation, crash recovery and native close faults
remain NOT_COVERED by these two proof cases. Nine journal exports still need
owner approval; no native admission or release readiness is claimed.
