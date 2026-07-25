# Simple Web Browser Production Hardening NFR Requirements

Selected scope: Option C - Release-Blocking Production Evidence NFRs.

## NFRs

| ID | NFR |
|----|-----|
| `NFR-WEB-HARD-001` | Production secret policy is fail-closed by default. |
| `NFR-WEB-HARD-002` | TLS mode forbids insecure local development fallback. |
| `NFR-WEB-HARD-003` | Origin checks happen before token minting, bearer verification, sensitive data return, or WebSocket upgrade. |
| `NFR-WEB-HARD-004` | Bearer verification is origin-bound and precedes any authenticated browser action. |
| `NFR-WEB-HARD-005` | Unauthenticated login/resume/body readers enforce bounded request sizes. |
| `NFR-WEB-HARD-006` | Live negative endpoint tests complete with deterministic child-process cleanup. |
| `NFR-WEB-HARD-007` | Warm browser authentication path latency is measured and reported when selected as a release target. |
| `NFR-WEB-HARD-008` | Live HTTP/WebSocket evidence records concrete status lines rather than placeholder passes. |
| `NFR-WEB-HARD-009` | Renderer parity evidence requires matching checksums, `mismatch_count=0`, and no blur/tolerance fallback. |
| `NFR-WEB-HARD-010` | Query-token bearer compatibility is non-authorizing in production and absent from generated production clients by default. |
| `NFR-WEB-HARD-011` | Login burst/rate behavior is bounded in normal and shared-WM server modes. |
| `NFR-WEB-HARD-012` | Platform GPU/browser evidence explicitly reports native pass, emulated pass, host-unavailable, structured-contract-only, or provenance-only status. |

## Evidence

The selected NFRs are traced in
`doc/03_plan/sys_test/simple_web_browser_production_hardening.md`.
macOS Metal, AMD ROCm/HIP, Windows DirectX, and real browser WebGPU native
device-readback proof remain external-host gates.

