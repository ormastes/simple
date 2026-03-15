# Web Security Library — Plan

**Requirement:** doc/requirement/web_security.md
**Design:** doc/design/web_security.md

## Objective

Create a reusable web security library (`src/lib/nogc_sync_mut/web_security/`) that any Simple web app can use for user auth, rate limiting, CSRF, input sanitization, and content safety.

## Current Status

| Component | Status | Evidence |
|-----------|--------|----------|
| HTTP Server FFI | Real | src/lib/nogc_sync_mut/io/http_ffi.spl |
| Session/Cookie | Real | src/lib/nogc_sync_mut/http_server/handler.spl |
| CORS Middleware | Real | src/lib/nogc_sync_mut/http_server/middleware.spl |
| User Storage | New | Not yet created |
| Password Hashing | New | Not yet created |
| Rate Limiter | New | Not yet created |
| CSRF Protection | New | Not yet created |
| Input Sanitizer | New | Not yet created |
| Content Safety | New | Not yet created |
| Security Logger | New | Not yet created |

## What To Do

1. Create user storage with SDN backend (difficulty: 2)
2. Implement password hashing via external process (difficulty: 2)
3. Implement session management with secure cookies (difficulty: 2)
4. Implement rate limiter with sliding window (difficulty: 2)
5. Implement CSRF token generation/validation (difficulty: 2)
6. Implement HTML input sanitizer (difficulty: 1)
7. Implement AI content safety filter (difficulty: 2)
8. Implement security event logger (difficulty: 1)
9. Integrate into hair_changer app (difficulty: 3)
10. Write tests (difficulty: 2)
