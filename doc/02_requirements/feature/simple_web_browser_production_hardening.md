# Simple Web Browser Production Hardening Feature Requirements

Selected scope: Option C - Full Browser Production Hardening.

## Requirements

| ID | Requirement |
|----|-------------|
| `REQ-WEB-HARD-001` | Production web servers require `SIMPLE_UI_WEB_TOKEN_SECRET` unless non-TLS local development explicitly opts into `SIMPLE_UI_WEB_ALLOW_INSECURE_DEV_SECRET=1`. |
| `REQ-WEB-HARD-002` | TLS web serving never uses the insecure development secret fallback. |
| `REQ-WEB-HARD-003` | `/ui/login` rejects missing or disallowed `Origin` before token minting. |
| `REQ-WEB-HARD-004` | Sensitive `/api/*` browser state routes require an allowed origin and valid bearer before returning state. |
| `REQ-WEB-HARD-005` | Production browser clients do not place bearer tokens in WebSocket URLs by default. |
| `REQ-WEB-HARD-006` | Live `/ui/login` negative requests cover missing origin, oversized unauthenticated bodies, and fail-closed status. |
| `REQ-WEB-HARD-007` | Live `/ui/ws` upgrades require allowed origin plus valid origin-bound bearer before HTTP 101, while legacy `/ws` and arbitrary WebSocket upgrade paths are hidden before upgrade. |
| `REQ-WEB-HARD-008` | Live `/ui/resume` rejects missing, malformed, or wrong-origin bearer requests before session resume. |
| `REQ-WEB-HARD-009` | Live sensitive `/api/state` and `/api/widgets` reject unauthenticated requests. |
| `REQ-WEB-HARD-010` | Live endpoint tests use stable port/process cleanup and real HTTP/WebSocket assertions. |
| `REQ-WEB-HARD-011` | `/ui/login` has bounded fixed-window burst/rate behavior in normal and shared-WM server modes. |
| `REQ-WEB-HARD-012` | Query-string bearer compatibility is non-authorizing in production, including when the deprecated `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` environment flag is present. |
| `REQ-WEB-HARD-013` | Production GUI/Web renderer parity evidence passes without marker, blur, or tolerance fallback. |
| `REQ-WEB-HARD-014` | GPU/browser environment evidence distinguishes native device readback from host-unavailable, emulated, structured-contract, or provenance-only rows. |

## Evidence

The selected requirements are traced in
`doc/03_plan/sys_test/simple_web_browser_production_hardening.md`.

