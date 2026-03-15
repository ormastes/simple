# Web Security Library — Design

**Requirement:** doc/requirement/web_security.md
**Plan:** doc/plan/web_security.md

## Architecture

```
src/lib/nogc_sync_mut/web_security/
  auth.spl                 # User registration, login, password verification
  session.spl              # Session create/validate/destroy with cookies
  rate_limiter.spl         # Per-IP/per-user rate limiting
  csrf.spl                 # CSRF token generation and validation
  sanitizer.spl            # XSS prevention, HTML escaping
  content_filter.spl       # AI content safety checks
  security_log.spl         # Security event logging
  middleware.spl            # Composable security middleware chain
  i18n_errors.spl          # Multi-language security error messages
```

## Type Definitions

### User
```simple
struct WebUser:
    id: text
    username: text
    password_hash: text
    role: text           # "user", "admin"
    created_at: text
    last_login: text
    is_active: bool
```

### SecurityEvent
```simple
struct SecurityEvent:
    timestamp: text
    event_type: text     # "login", "logout", "failed_login", "rate_limited", "csrf_fail"
    username: text
    ip_address: text
    details: text
```

## API Surface

| Function | Module | Description |
|----------|--------|-------------|
| `auth_register(username, password)` | auth | Register new user |
| `auth_login(username, password)` | auth | Verify credentials, return session |
| `auth_check_session(session_id)` | session | Validate active session |
| `rate_check(ip, limit, window_sec)` | rate_limiter | Check if request allowed |
| `csrf_generate()` | csrf | Generate CSRF token |
| `csrf_validate(token)` | csrf | Validate CSRF token |
| `sanitize_html(input)` | sanitizer | Escape HTML special chars |
| `content_is_safe(prompt)` | content_filter | Check AI prompt safety |
| `security_log(event)` | security_log | Log security event |
| `security_error_msg(code, lang)` | i18n_errors | Get localized error |
