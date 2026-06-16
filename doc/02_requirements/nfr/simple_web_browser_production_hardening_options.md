# Simple Web Browser Production Hardening NFR Options

## Selection Instructions

Select exactly one NFR scope: A, B, or C. After selection, write the final NFR
file at `doc/02_requirements/nfr/simple_web_browser_production_hardening.md`,
delete this options file, and preserve only the selected candidate NFR IDs.

Candidate IDs are cumulative by option:

- Option A selects `NFR-WEB-HARD-001` through `NFR-WEB-HARD-004`.
- Option B selects Option A plus `NFR-WEB-HARD-005` through
  `NFR-WEB-HARD-008`.
- Option C selects Option B plus `NFR-WEB-HARD-009` through
  `NFR-WEB-HARD-012`.

## Candidate NFRs

| ID | Candidate NFR | First option |
|----|---------------|--------------|
| `NFR-WEB-HARD-001` | Production secret policy is fail-closed by default. | A |
| `NFR-WEB-HARD-002` | TLS mode forbids insecure local development fallback. | A |
| `NFR-WEB-HARD-003` | Origin checks happen before token minting, bearer verification, sensitive data return, or WebSocket upgrade. | A |
| `NFR-WEB-HARD-004` | Bearer verification is origin-bound and precedes any authenticated browser action. | A |
| `NFR-WEB-HARD-005` | Unauthenticated login/resume/body readers enforce bounded request sizes. | B |
| `NFR-WEB-HARD-006` | Live negative endpoint tests complete with deterministic child-process cleanup. | B |
| `NFR-WEB-HARD-007` | Warm browser authentication path latency is measured and reported when selected as a release target. | B |
| `NFR-WEB-HARD-008` | Live HTTP/WebSocket evidence records concrete status lines rather than placeholder passes. | B |
| `NFR-WEB-HARD-009` | Renderer parity evidence requires matching checksums, `mismatch_count=0`, and no blur/tolerance fallback. | C |
| `NFR-WEB-HARD-010` | Query-token bearer compatibility is opt-in only and absent from generated production clients by default. | C |
| `NFR-WEB-HARD-011` | Login burst/rate behavior is bounded in normal and shared-WM server modes. | C |
| `NFR-WEB-HARD-012` | Platform GPU/browser evidence explicitly reports native pass, emulated pass, host-unavailable, structured-contract-only, or provenance-only status. | C |

## Option A: Security Fail-Closed NFRs

Targets:
- Missing production token secret fails startup.
- TLS serving never uses insecure development fallback.
- Missing/disallowed Origin fails before token minting or WebSocket upgrade.
- Bearer token verification happens before sensitive data or upgrade success.

Pros:
- Clear and directly testable.
- Matches the current security-boundary implementation.

Cons:
- Does not set live latency, request-size, or abuse-control targets.

Effort: Low.

## Option B: Security Plus Runtime Robustness NFRs

Targets:
- Option A targets.
- Login/resume/body readers reject oversized unauthenticated request bodies.
- Live negative endpoint tests must complete without leaked child processes.
- Warm browser auth path latency is measured and reported.

Pros:
- Covers practical production abuse and operational risk.
- Gives verification stronger runtime evidence.

Cons:
- Requires process and port hygiene in tests.
- May require new helper infrastructure for stable measurements.

Effort: Medium.

## Option C: Release-Blocking Production Evidence NFRs

Targets:
- Option B targets.
- Full production GUI/Web renderer parity wrapper passes with
  `mismatch_count=0`, matching checksums, and no blur/tolerance fallback.
- Query-token bearer fallback is disabled by default or proven unavailable in
  generated production clients.
- `/ui/login` has bounded burst/rate behavior.

Pros:
- Strongest production-readiness bar.
- Aligns auth hardening and renderer parity under one release gate.

Cons:
- Renderer parity is passing locally now, but selecting this option makes that
  evidence release-blocking.
- More expensive to run and debug.

Effort: High.
