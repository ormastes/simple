# Machine managed scope V1 neutral durable records

Status: **AUTHORED_NOT_RUN**. Mirrors
`test/01_unit/lib/container/machine_managed_scope_record_v1_spec.spl`.
No compiler, runtime, native fixture, storage writer or doc generator ran.

These tests exercise production canonical-record, strict-replay and existing
Host capacity-accounting functions with explicit pure metadata fixtures. They
create no installed-policy owner, verified credential, machine claim, execution
grant or workload. Numbered fixture rows model WAL sequence assignment only.

| Requirement | Authored assertions |
|---|---|
| REQ-MACHINE-MANAGED-SCOPE-001 | Canonical scope binds policy and trust-policy digests, verified issuer metadata, exact enrollment/credential digests, physical/native/service/provider identity and generation, complete CPU/memory ceiling and signed deadline. Same issuer with different key policy changes the record. |
| REQ-MACHINE-MANAGED-SCOPE-002 | Existing `host_available_capacity_v1` charges an Uncertain reservation with `continuity_proven: false`; either exceeded resource ceiling, wrong physical host or wrong generation refuses. No invented continuity or native absence evidence. |
| REQ-MACHINE-MANAGED-SCOPE-003 | One scope and one reservation row form one immutable transaction. Exact replay succeeds; altered bindings, missing/additional/reordered rows and a purported release refuse. Initial publication requires authorization before the deadline; retained replay does not release expired charges. |

The machine authority separately requires actual retained native policy,
physical-capacity observation, provider observation and a private verified
enrollment proof. It compares the actual enrollment-policy digest to the
machine-installed V2 trust pin and compares verified issuer to the installed
managed authority before committing these records through the existing machine
WAL. Recovery-only proof cannot create a missing charge. Public record values
and public claim snapshots are data, never capabilities.

The bounded claim history supports one exact whole-scope delegation. It rejects
unknown or changed history without clearing prior charges. The signed physical
ceiling includes the Host broker partition; nested Host accounting subdivides
that ceiling. Owner close releases the writer while leaving the durable rows.
No absence, settlement, deletion, capacity-release or policy-migration API is
introduced by these fixtures.

Actual wrong-key crypto, competing native writers, crash/CAS ambiguity, retained
cleanup and enrollment-to-Host composition remain separate authored native
scenarios and **NOT_RUN**. The pure fixtures cannot certify those boundaries.
