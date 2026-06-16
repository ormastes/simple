# Simple Web Browser Production Hardening Feature Requirement Options

## Option A: Auth Boundary Only

Selected scope would cover production secrets, Origin fail-closed behavior,
origin-bound bearer tokens, sensitive API route gating, and generated browser
clients avoiding token URLs.

Pros:
- Smallest production security slice.
- Mostly covered by current unit evidence.
- Low risk of pulling renderer parity work into auth changes.

Cons:
- Does not prove live endpoint behavior.
- Leaves renderer parity and request-size hardening outside the selected scope.
- Query-token compatibility may remain longer than desired.

Effort: Low to medium.

## Option B: Auth Boundary Plus Live Endpoint Evidence

Selected scope would include Option A plus live HTTP/WebSocket negative tests
for `/ui/login`, `/ui/ws`, `/ws`, `/ui/resume`, sensitive `/api/*`, malformed
tokens, wrong origins, and oversized unauthenticated bodies.

Pros:
- Stronger production evidence for the actual browser boundary.
- Directly addresses the highest remaining test gap.
- Keeps renderer parity as a separately measured gate.

Cons:
- Requires stable test ports/process cleanup.
- May expose existing server lifecycle flakes before security assertions run.

Effort: Medium.

## Option C: Full Browser Production Hardening

Selected scope would include Option B plus rate/burst control for `/ui/login`,
query-token fallback retirement or explicit compatibility gating, and passing
production GUI/Web renderer parity evidence.

Pros:
- Closest match to "production level" across auth and renderer evidence.
- Leaves fewer known browser-facing risks.
- Creates a clear release-blocking target.

Cons:
- Highest blast radius.
- Renderer layout parity is currently failing broadly and may require a
  separate rendering implementation lane.
- More likely to need multiple iterations and platform-specific evidence.

Effort: High.
