# Simple Web Browser Production Hardening NFR Options

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
- Renderer parity currently fails layout manifest evidence.
- More expensive to run and debug.

Effort: High.
