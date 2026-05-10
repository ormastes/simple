# Security AOP Architecture — Implementation Complete

**Date:** 2026-03-28
**Phases completed:** 1-15

## Artifacts

| Type | Path |
|------|------|
| Requirement | doc/02_requirements/feature/security_aop.md |
| Research | doc/01_research/security_aop_architecture_2026-03-28.md |
| NFR | doc/02_requirements/nfr/security_baseline.md |
| Design | doc/05_design/security_aop.md |
| System Tests | test/system/security_aop_spec.spl |
| Unit Tests | test/unit/lib/security/sanitize_spec.spl |
| Unit Tests | test/unit/lib/security/audit_log_spec.spl |
| Unit Tests | test/unit/lib/http_server/csrf_spec.spl |
| Unit Tests | test/unit/lib/http_server/rate_limit_spec.spl |
| Unit Tests | test/unit/lib/http_server/security_headers_spec.spl |
| Unit Tests | test/unit/lib/http_server/request_validation_spec.spl |
| Unit Tests | test/unit/app/ui/capability_policy_spec.spl |
| Bug Report | doc/08_tracking/bug/security_aop_limitations.md |

## Source Files

### New Files (28)

**Security Core Library (6)**
- src/lib/common/security/mod.spl
- src/lib/common/security/types.spl
- src/lib/common/security/audit_log.spl
- src/lib/common/security/sanitize.spl
- src/lib/common/security/capsule.sdn
- src/lib/common/security/aspects/mod.spl

**AOP Aspects (3)**
- src/lib/common/security/aspects/audit_advice.spl
- src/lib/common/security/aspects/auth_advice.spl
- src/lib/common/security/aspects/validation_advice.spl

**HTTP Security Middleware (5)**
- src/lib/nogc_async_mut/http_server/rate_limit.spl
- src/lib/nogc_async_mut/http_server/request_validation.spl
- src/lib/nogc_async_mut/http_server/csrf.spl
- src/lib/nogc_async_mut/http_server/cors.spl
- src/lib/nogc_async_mut/http_server/security_headers.spl

**UI Security (2)**
- src/lib/common/ui/capability_policy.spl
- src/lib/common/ui/capability_config.spl

**Tests (8)**
- test/system/security_aop_spec.spl
- test/unit/lib/security/sanitize_spec.spl
- test/unit/lib/security/audit_log_spec.spl
- test/unit/lib/http_server/csrf_spec.spl
- test/unit/lib/http_server/rate_limit_spec.spl
- test/unit/lib/http_server/security_headers_spec.spl
- test/unit/lib/http_server/request_validation_spec.spl
- test/unit/app/ui/capability_policy_spec.spl

**Documentation (4)**
- doc/02_requirements/nfr/security_baseline.md
- doc/02_requirements/feature/security_aop.md
- doc/01_research/security_aop_architecture_2026-03-28.md
- doc/05_design/security_aop.md

### Modified Files (8)
- src/lib/common/ui/capability.spl — Expanded from 6 to 20 variants
- src/lib/common/ui/session.spl — Added capability_policy field + enforcement
- src/app/ui.tauri/backend.spl — Capability checks before IPC ops
- src/app/ui.ipc/protocol.spl — IPC message validation
- src/compiler/85.mdsoc/weaving/weaving_config.spl — Security aspects factory
- src/compiler/85.mdsoc/weaving/join_point_kind.spl — SecurityGate variant
- src/lib/nogc_async_mut/http_server/cors.spl — Dedup: imports get_header_value from csrf

## Test Results
- System tests: 130 passed, 0 failed
- Unit tests: 61 passed, 0 failed
- Total: **191 passed, 0 failed**
- Duration: < 100ms total

## Duplication
- Token (jscpd): 0% — no 5-line duplicates found
- Semantic: cors.spl get_header() was duplicate of csrf.spl get_header_value() — fixed (imports from csrf)

## Stub Prevention
- STUB001 warnings: 0 (all functions use their parameters)
- pass_todo count: 0
- pass_do_nothing count: 0
- Identity-return functions: 0
- All functions are fully implemented

## Limitations Found
- L-1: Rate limiter state not persistent (in-memory only)
- L-2: CSRF requires session middleware to run first
- L-3: AOP weaving requires compiled mode (not interpreter)
- L-4: Capability policy not hot-reloadable
- L-5: Security headers need response wrapper integration
- L-6: HTML sanitizer doesn't handle exotic Unicode attacks
- L-7: Capsule SDN uses line-based parser

See doc/08_tracking/bug/security_aop_limitations.md for details.

## Architecture Summary

Security is now a **first-class MDSOC dimension** with 5 orthogonal layers:
```
audit (highest)     — observes all via AOP, no direct deps
auth                — session, CSRF, identity
validation          — input sanitization, request checks
enforcement         — capability gates, permission checks
crypto (lowest)     — pure primitives (HMAC, SHA, random)
```

3 AOP aspects weave security at compile time:
- **audit_advice** — Around/After for request + auth logging
- **auth_advice** — Before for @requires_auth enforcement
- **validation_advice** — Around for HTML output sanitization

Business modules contain **zero security imports**.
