# Hair Changer + Web Security — Known Limitations

**Date:** 2026-03-15
**Features:** hair_changer, web_security

## Limitations

### L1: Self-contained main.spl exceeds 800-line guideline
- **Severity:** Low
- **Description:** The interpreter loads a single file, so main.spl must inline all MDSOC module code. simple_aidev/main.spl is 1244 lines. The MDSOC directory structure provides logical separation but the runtime file is monolithic.
- **Workaround:** MDSOC files in entity/, feature/, transform/, shared/ are the canonical source. main.spl is the assembled output.
- **Related:** Interpreter single-file limitation

### L2: Password hashing is demo-quality (DJB2-like)
- **Severity:** High (for production use)
- **Description:** The `_simple_hash()` function uses a DJB2-like hash for password storage. This is NOT cryptographically secure and should never be used in production.
- **Workaround:** For production, use `rt_process_run("python3", ["-c", "import bcrypt; print(bcrypt.hashpw(...))"])` or implement bcrypt via SFFI to Rust's `bcrypt` crate.
- **Related:** No crypto FFI primitives in Simple runtime

### L3: Session tokens are predictable
- **Severity:** High (for production use)
- **Description:** `_generate_token()` uses a simple hash of the username + counter. Tokens are predictable and not cryptographically random.
- **Workaround:** For production, use `rt_process_run("openssl", ["rand", "-hex", "32"])` to generate secure random tokens, or add `rt_crypto_random_bytes(n)` FFI.
- **Related:** No CSPRNG in Simple runtime

### L4: Rate limiter has no time-based window reset
- **Severity:** Medium
- **Description:** The rate limiter counts requests per IP but doesn't automatically reset the window based on time. Requires manual `rate_reset_all()` calls.
- **Workaround:** Call `rate_reset_all()` periodically from a timer or at the start of each request cycle.
- **Related:** No background timer/scheduler in interpreter mode

### L5: Content safety filter is keyword-based only
- **Severity:** Medium
- **Description:** The content filter uses simple keyword matching (`contains()`) which can be bypassed with misspellings, unicode tricks, or obfuscation. No semantic understanding.
- **Workaround:** For production, use Gemini's built-in safety filters (`safetySetting` parameter) as a second layer. Consider calling an external moderation API.
- **Related:** Gemini API has built-in content safety

### L6: HTTP server not integrated in interpreter mode
- **Severity:** Medium
- **Description:** The `rt_http_server_*` FFI functions exist but may not work in interpreter mode. The CLI falls back to suggesting `python3 -m http.server`.
- **Workaround:** Use compiled mode (`bin/simple build` then run binary) for full HTTP server, or use Python/nginx as a reverse proxy during development.
- **Related:** Interpreter mode limitations

### L7: `continue` in while loops skips increment
- **Severity:** P2
- **Description:** Using `continue` inside a `while` loop skips the loop variable increment (`i = i + 1`), causing infinite loops. This is a language-level issue.
- **Workaround:** Avoid `continue`. Use `if not condition:` with the logic inside the else branch, or restructure with boolean flags.
- **Related:** test/bug/interp_double_exec_spec.spl pattern

### L8: No HTTPS/TLS server support
- **Severity:** High (for production)
- **Description:** The Simple runtime has TLS client support but no TLS server. All HTTP traffic is unencrypted.
- **Workaround:** Use a reverse proxy (nginx, caddy) with TLS termination in front of the Simple HTTP server.
- **Related:** src/lib/nogc_sync_mut/tls/ is incomplete

## Summary

| # | Limitation | Severity | Mitigation |
|---|-----------|----------|-----------|
| L1 | Monolithic main.spl | Low | MDSOC logical split |
| L2 | Demo password hashing | High* | Use bcrypt via FFI/process |
| L3 | Predictable tokens | High* | Use openssl rand |
| L4 | No time-window rate limit | Medium | Manual reset |
| L5 | Keyword-only content filter | Medium | Gemini safety API |
| L6 | No HTTP server in interp | Medium | Compiled mode or proxy |
| L7 | continue skips increment | P2 | Avoid continue |
| L8 | No HTTPS server | High* | Reverse proxy |

*High severity items are production concerns only. For demo/development use, current implementation is adequate.
