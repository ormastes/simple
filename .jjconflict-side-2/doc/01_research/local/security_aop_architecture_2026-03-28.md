# Security AOP Architecture — Research

**Date:** 2026-03-28
**Related Requirement:** [doc/02_requirements/feature/security_aop.md](../plan/requirement/security_aop.md)
**Related NFR:** [doc/02_requirements/nfr/security_baseline.md](../plan/nfr/security_baseline.md)
**Related Design:** [doc/05_design/security_aop.md](../design/security_aop.md)

## Research Summary

### Existing Security Foundations

The Simple language project already has significant security infrastructure:

1. **Parser Security** — SDN parser operates in data-only mode by default (prevents RCE, injection, DoS). Documented in `doc/01_research/data_format_parser_security_2026-01-31.md`.

2. **Sandbox Strategies** — Hybrid native OS (Linux namespaces) + bubblewrap approach documented in `doc/01_research/sandbox_implementation_strategies.md`.

3. **Memory Safety** — 3-phase plan (warning → refactor → strict mode) in `doc/03_plan/manual_memory_safety_plan.md`. Borrow checker at `src/compiler/55.borrow/` with NLL, borrow graph, lifetime analysis, GC analysis.

4. **Crypto FFI** — Ring/Argon2 bindings in `src/lib/nogc_sync_mut/io/crypto_ffi.spl` providing SHA-256/512, BLAKE3, HMAC, Argon2id, Bcrypt, AES-256-GCM, PBKDF2, CSPRNG.

5. **Self-Protecting Test Runner** — Resource daemon with IPC server, Unix socket (0600), PID validation.

6. **Fuzzing Framework** — Cargo-fuzz for lexer/parser/codegen, cargo-mutants for test quality.

### Gap Analysis

| Gap | Impact | Solution |
|-----|--------|----------|
| No MDSOC security capsules | Security not orthogonally composed | New security dimension with 5 capsules |
| No security NFRs | No measurable quality targets | `doc/02_requirements/nfr/security_baseline.md` |
| No audit logging | No security observability | AOP audit aspect woven at join points |
| No CSRF/XSS protection | Web server vulnerable | HTTP middleware stack |
| Minimal UI capabilities | No enforcement, only 6 enum variants | Expand to 20+, add policy engine |
| No IPC validation | Message injection risk | Size/structure validation |
| No security headers | Missing CSP, HSTS, etc. | Security headers middleware |

### AOP Architecture Decision

**Why AOP for security?** Security is the textbook cross-cutting concern:
- Audit logging touches every handler, every auth flow, every sensitive operation
- Auth checks gate every protected endpoint
- Input validation must run before every render, every data store
- Without AOP, developers must manually add security calls — error-prone and inconsistent

**MDSOC Advantage:** The security dimension is orthogonal to feature dimensions. Business modules have zero security imports. The compiler weaves security at MIR level using matched join points, guaranteeing coverage.

**5-Layer Design:**
```
audit (highest)     — observes all, depends on none
auth                — session, CSRF, identity
validation          — input sanitization, request checks
enforcement         — capability gates, permission checks
crypto (lowest)     — pure primitives, no side effects
```

Layer rules prevent upward dependencies (crypto cannot import from audit). The audit layer specifically does NOT directly call auth — it observes auth events through AOP weaving.

### HTTP Middleware Phase Mapping

The async HTTP server already has an nginx-style 7-phase pipeline. Security middleware maps naturally:

| Security Middleware | HTTP Phase | Priority | Why This Phase |
|--------------------|-----------|----------|----------------|
| Rate Limiting | PreRead | 100 | Reject before reading body |
| Request Validation | Read | 90 | Validate after body read |
| CSRF Protection | Access | 150 | Check before handler |
| CORS | Access | 180 | Set headers before handler |
| Security Headers | Access | 200 | Add headers to all responses |

### Risks and Mitigations

| Risk | Mitigation |
|------|-----------|
| AOP weaving performance overhead | NFR: < 1ms P95 per middleware; audit logging is async-safe |
| False-positive CSRF rejections | Double-submit cookie pattern; exempt safe methods; thorough testing |
| Capability enum expansion breaks backends | Backward-compatible: new variants added after existing ones |
| Capsule config parsing errors | SDN format already battle-tested; add validation tests |
