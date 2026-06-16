# Simple Web Browser Production Hardening Feature Requirement Options

## Selection Instructions

Select exactly one feature scope: A, B, or C. After selection, write the final
feature requirement file at
`doc/02_requirements/feature/simple_web_browser_production_hardening.md`,
delete this options file, and preserve only the selected candidate REQ IDs.

Candidate IDs are cumulative by option:

- Option A selects `REQ-WEB-HARD-001` through `REQ-WEB-HARD-005`.
- Option B selects Option A plus `REQ-WEB-HARD-006` through
  `REQ-WEB-HARD-010`.
- Option C selects Option B plus `REQ-WEB-HARD-011` through
  `REQ-WEB-HARD-014`.

## Candidate Feature Requirements

| ID | Candidate requirement | First option |
|----|-----------------------|--------------|
| `REQ-WEB-HARD-001` | Production web servers require `SIMPLE_UI_WEB_TOKEN_SECRET` unless non-TLS local development explicitly opts into `SIMPLE_UI_WEB_ALLOW_INSECURE_DEV_SECRET=1`. | A |
| `REQ-WEB-HARD-002` | TLS web serving never uses the insecure development secret fallback. | A |
| `REQ-WEB-HARD-003` | `/ui/login` rejects missing or disallowed `Origin` before token minting. | A |
| `REQ-WEB-HARD-004` | Sensitive `/api/*` browser state routes require an allowed origin and valid bearer before returning state. | A |
| `REQ-WEB-HARD-005` | Production browser clients do not place bearer tokens in WebSocket URLs by default. | A |
| `REQ-WEB-HARD-006` | Live `/ui/login` negative requests cover missing origin, oversized unauthenticated bodies, and fail-closed status. | B |
| `REQ-WEB-HARD-007` | Live `/ui/ws` and legacy `/ws` upgrades require allowed origin plus valid origin-bound bearer before HTTP 101. | B |
| `REQ-WEB-HARD-008` | Live `/ui/resume` rejects missing, malformed, or wrong-origin bearer requests before session resume. | B |
| `REQ-WEB-HARD-009` | Live sensitive `/api/state` and `/api/widgets` reject unauthenticated requests. | B |
| `REQ-WEB-HARD-010` | Live endpoint tests use stable port/process cleanup and real HTTP/WebSocket assertions. | B |
| `REQ-WEB-HARD-011` | `/ui/login` has bounded fixed-window burst/rate behavior in normal and shared-WM server modes. | C |
| `REQ-WEB-HARD-012` | Query-string bearer compatibility is disabled by default and enabled only by explicit `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1`. | C |
| `REQ-WEB-HARD-013` | Production GUI/Web renderer parity evidence passes without marker, blur, or tolerance fallback. | C |
| `REQ-WEB-HARD-014` | GPU/browser environment evidence distinguishes native device readback from host-unavailable, emulated, structured-contract, or provenance-only rows. | C |

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
- Renderer parity is passing locally now, but selecting this option makes it a
  release-blocking gate instead of separate supporting evidence.
- More likely to need multiple iterations and platform-specific evidence.

Effort: High.
