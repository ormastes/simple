# Security AOP Architecture — Requirements

**Feature:** MDSOC/AOP Security Dimension for UI and Web Server
**Date:** 2026-03-28
**Status:** In progress

## Motivation

Security concerns (audit logging, authentication checks, input validation, capability enforcement) are cross-cutting — they affect HTTP handlers, UI rendering, IPC protocols, and file operations. Without AOP, security code is duplicated across modules and easily forgotten. By making security a first-class MDSOC dimension, security aspects are woven at compile time, ensuring zero-gap coverage with zero security code in business modules.

## Scope

### In Scope

1. **Security MDSOC Dimension** — 5-layer capsule (crypto, enforcement, validation, auth, audit) with compile-time weaving
2. **HTTP Security Middleware** — Rate limiting, CSRF, CORS, security headers, request validation for the async HTTP server
3. **UI Capability Enforcement** — Default-deny capability policy engine, SDN config, per-window enforcement in Tauri/session
4. **AOP Security Aspects** — Audit logging, auth checking, output sanitization woven at matched join points
5. **Input Sanitization Library** — HTML, URL, path, identifier sanitization
6. **Security Core Types** — SecurityEvent enum, AuditEntry, SecurityContext, AuditConfig
7. **Security NFR** — Measurable quality constraints for all security features

### Out of Scope (v1)

- Formal verification of borrow checker / parser correctness
- Signed binary verification / reproducible builds
- Certificate pinning
- Full WAF (Web Application Firewall) functionality
- OAuth2/OIDC provider implementation (existing OAuth client is sufficient)

## Acceptance Criteria

1. **AC-1:** Security dimension with 5 capsules is defined in capsule.sdn and parseable
2. **AC-2:** 3 AOP aspects (audit, auth, validation) weave at correct join points
3. **AC-3:** 5 HTTP security middleware plug into existing MiddlewarePipeline phases
4. **AC-4:** UI capability enum expanded to 20+ variants with policy enforcement
5. **AC-5:** Default-deny capability policy blocks ungranteds, explicit grants pass
6. **AC-6:** Tauri backend enforces capability checks before IPC operations
7. **AC-7:** IPC message validation rejects oversized/malformed messages
8. **AC-8:** Input sanitization prevents XSS (< > & " ' / escaped)
9. **AC-9:** All security events logged as structured JSON audit entries
10. **AC-10:** SecurityGate join point kind added to MDSOC weaving system

## Dependencies

| Module | Path | Used For |
|--------|------|----------|
| Crypto FFI | `src/lib/nogc_sync_mut/io/crypto_ffi.spl` | HMAC-SHA256, random bytes |
| MDSOC weaving | `src/compiler/85.mdsoc/weaving/` | Join points, advice, weaving rules |
| MDSOC config | `src/compiler/85.mdsoc/config.spl` | Capsule SDN parsing |
| Async HTTP server | `src/lib/nogc_async_mut/http_server/` | Middleware pipeline |
| UI session | `src/lib/common/ui/session.spl` | Capability policy integration |
| Tauri backend | `src/app/ui.tauri/backend.spl` | Capability enforcement |
| IPC protocol | `src/app/ui.ipc/protocol.spl` | Message validation |

## Related Documents

- Design: [doc/05_design/security_aop.md](../../05_design/security_aop.md)
- NFR: [doc/02_requirements/nfr/security_baseline.md](../nfr/security_baseline.md)
- Research: [doc/01_research/local/security_aop_architecture_2026-03-28.md](../../01_research/local/security_aop_architecture_2026-03-28.md)
- Research: [doc/01_research/data_format_parser_security_2026-01-31.md](../../01_research/data_format_parser_security_2026-01-31.md)
- Research: [doc/01_research/sandbox_implementation_strategies.md](../../01_research/sandbox_implementation_strategies.md)
- Tauri Req: [doc/02_requirements/feature/simple_tauri.md](simple_tauri.md)
