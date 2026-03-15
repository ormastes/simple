# Web Security Library — Requirements

**Feature:** Common web security library for Simple language applications
**Location:** `src/lib/nogc_sync_mut/web_security/` (library) + integration into hair_changer

## Motivation

All Simple web apps need: user authentication, session management, rate limiting, input validation, CSRF protection, and content safety filters. Currently each app re-implements these ad-hoc. A common library prevents security gaps.

## Scope

### In Scope
- User registration/login with secure password hashing (simulated via process call to external hasher)
- Session management with secure cookies
- Rate limiting (per-IP, per-user)
- CSRF token generation and validation
- Input sanitization (XSS prevention)
- Content safety filter for AI image generation (prompt injection, inappropriate content)
- Request logging for security audit
- Multi-language error messages (ko/en/ja)

### Out of Scope
- OAuth2 social login (existing scaffold can be extended later)
- HTTPS/TLS server (client TLS exists)
- Email verification
- Two-factor authentication

## Acceptance Criteria

- AC-1: User can register with username + password
- AC-2: User can login and receive session cookie
- AC-3: Protected endpoints reject unauthenticated requests
- AC-4: Rate limiter blocks excessive requests (configurable threshold)
- AC-5: CSRF tokens are validated on state-changing requests
- AC-6: HTML special chars are escaped in user input
- AC-7: AI content safety filter blocks prohibited prompts
- AC-8: Security events are logged
- AC-9: All error messages support ko/en/ja
- AC-10: Library is reusable across Simple web apps

## Dependencies
- `src/lib/nogc_sync_mut/http_server/` — existing HTTP primitives
- `src/lib/nogc_sync_mut/database/` — SDN storage for users
- `rt_process_run` — for calling external crypto tools

## OWASP Top 10:2025 Coverage

| Risk | Mitigation |
|------|-----------|
| A01 Broken Access Control | Session-based auth, role checks |
| A02 Security Misconfiguration | Secure defaults, CORS |
| A05 Injection | Input sanitization, parameterized queries |
| A07 Authentication Failures | Secure password hashing, session management |
| A09 Logging Failures | Security event logging |
| A10 Exceptional Conditions | Proper error handling, safe defaults |
