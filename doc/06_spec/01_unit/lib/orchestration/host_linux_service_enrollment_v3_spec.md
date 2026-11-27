# Linux service enrollment contract

Status: AUTHORED_NOT_RUN. This manual describes seven executable pure-contract
scenarios in `test/01_unit/lib/orchestration/host_linux_service_enrollment_v3_spec.spl`.
It is not generated execution evidence and does not attest filesystem ownership,
signatures, native identity, journal admission, or service readiness.

| Requirement | Executable scenario | Expected evidence |
| --- | --- | --- |
| LINUX-SERVICE-ENROLLMENT-01 | roundtrips canonical bytes and derives exact allocatable capacity | Canonical re-encoding and SHA digest match. |
| LINUX-SERVICE-ENROLLMENT-01 | rejects Windows legacy and native-boot schema substitutions | Exact version/mode refusal. |
| LINUX-SERVICE-ENROLLMENT-01 | does not admit boot epoch or generation as static enrollment fields | Each dynamic field is rejected as unknown. |
| LINUX-SERVICE-CAPACITY-01 | rejects exhausted negative and overflow-shaped capacity before subtraction | Exact partition refusal for CPU and memory. |
| LINUX-SERVICE-ENROLLMENT-01 | rejects traversal aliases and byte oversized installed parent paths | Native absolute spelling and UTF-8 byte boundary enforced. |
| LINUX-SERVICE-ENROLLMENT-01 | rejects noncanonical oversized malformed and wrong typed input | Distinct size, canonical, parser, and field-type paths. |
| LINUX-SERVICE-ENROLLMENT-01 | binds engine provider capacity and policy changes into distinct digests | Each semantic mutation changes the canonical binding digest. |

Owner-level integration must separately verify a current signed enrollment,
the genuine retained native identity, original protected journal custody,
physical capacity, and exact service-to-execution association. Historical
enrollment admission may support recovery only; it does not authorize new work.
