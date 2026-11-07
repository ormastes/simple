# Static signed service enrollment — authored specification

Status: **NOT_RUN / AWAITING_VERIFICATION**. Authored manual, not generated runtime evidence. No builds, tests or native commands ran. All local editing/static commands used shared CPU affinity 0–4.

Source: `test/03_system/app/orchestrator/feature/host_service_enrollment_spec.spl` (seven cases).

| Requirement | Authored real prevention cases |
| --- | --- |
| HOST-SERVICE-ENROLLMENT-01 | Real Ed25519 grant+approval acceptance; exact canonical roundtrip; changed raw engine pin/broker pin fails original signature binding; actual signature corruption, exact approval expiry and policy revision drift reject. Strict unknown/noncanonical/oversized input, wrong backend and relative/traversing parent reject. Observed Windows namespaced native ID roundtrips without inventing continuity. |
| HOST-SERVICE-BROKER-PARTITION-01 | Positive signed physical-minus-broker partition returns 1900 millicpu and 384 bytes from 2000/512 minus 100/128; zero/negative/exhausted/overflow-shaped reservation rejects before subtraction. Changed CPU or memory partition rejects original signed binding. |
| HOST-SERVICE-ENGINE-PIN-01 | Exact raw engine bytes SHA256 roundtrips in required enginePolicyDigest; removing the actual canonical wire field rejects missing-field; empty/short/uppercase/multibyte/oversized pins reject; changing valid pin rejects the original signed envelope. |

These are pure codec/arithmetic plus actual cryptographic verification assertions. They do not read an engine policy or authenticate an arbitrary root. Static installed policy pins never imply Windows ACL ownership, native process/job limits, boot-counter continuity, service readiness, provider liveness, or broker enforcement. A fresh service incarnation belongs to the actual startup factory and is absent from this signed static schema. The broker partition is deducted once by its capacity consumer, never once per helper.

Missing runtime evidence: all seven source cases, actual Windows native root loading/enrollment, installed raw engine/broker byte comparison, broker/job capability enforcement, fresh epoch startup, same-journal reconciliation and supported platform builds. Claim/root WIP is not included. No runtime PASS, power-loss durability or full persistent-host claim is made.
