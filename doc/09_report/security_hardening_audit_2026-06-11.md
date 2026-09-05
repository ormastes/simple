# Security Hardening Audit — 2026-06-11

Parallel audit (6 Sonnet agents, disjoint scopes) of Simple stdlib, web-app infra,
AOP, and SimpleOS kernel. Findings reviewed by orchestrator before any commit.

## LANDED (committed — fixes verified, no broken callers)

Commit `kmv88` (sec, weaving_config) + swept into `90c586f08a` by a concurrent
jj reconcile (content correct in tree; attribution split, not re-grouped to avoid
racing the active parallel agent).

### AOP / weaving — fail-open enforcement
- **CRITICAL fail-open**: `auth_advice.check_auth_before`, `check_capability_before`,
  and `deny_advice.deny_all_before` declared no return type → `return Err(...)` was
  typed `void`; the weaver's `is_err()` denial gate could never fire. Added
  `-> Result<(), text>`. (auth_advice.spl, deny_advice.spl)
- **HIGH**: `deny_all_before` advice existed but was never wired into the weaving
  before-advice list — `@deny_all` endpoints were unprotected. Wired at priority 850
  ahead of `auth_check`. (weaving_config.spl)
- **CRITICAL**: `init_aop()` had no idempotency guard — a second call wiped the
  registry, removing all registered security aspects. Added `is_some()` guard.
- `unregister`/`disable` on the global `AspectRegistry` renamed to `*_unsafe` and
  moved into a proper `impl` block (were nested in `time_now_ms` body).
- `_glob_match` suffix overlap bug (`a*a` matched `a`) — under-matched security pointcuts.

### Capability enforcement — fail-open authorization
- **CRITICAL**: `parse_capability` returned `Custom(scope: "*")` for malformed/unknown
  input → unknown strings silently became wildcard-matchable grants. Now returns
  `Result`; malformed/unknown → `Err`. (enforcement/capability.spl)
- **HIGH path-confusion**: `_capability_path_allowed` used `starts_with(scope)` → scope
  `/data` matched `/data-evil`. Now uses separator boundary `scope + "/"`.

### Web / HTTP middleware
- **CRITICAL CORS**: wildcard `*` + reflected Origin + `Allow-Credentials: true` = full
  auth bypass. Now blocks wildcard+credentials, rejects `null` origin, emits literal `*`.
- **CRITICAL CRLF**: `validate_headers` did not check `\r`/`\n` → response-splitting /
  header injection. Added `contains_crlf` (raw + `%0d`/`%0a`).
- **HIGH**: CSRF token compared with `!=` (timing oracle) → constant-time compare;
  cookie value truncated on every `=` → split on first `=` only.
- **HIGH**: rate-limit divide-by-zero on `window_ms == 0`; HSTS `max-age` clamped ≥ 1y;
  dropped `unsafe-inline` from default `style-src` CSP.

### Sanitize / validation
- **HIGH**: `sanitize_url` blocklist allowed `ftp:`/`gopher:` via "no `://` = relative"
  fallthrough → switched to allowlist (`http`, `https`, `/`, `#`).
- **HIGH**: `sanitize_path` allowed absolute paths (`/`, `C:\`) and mixed-case `%2E%2e`
  traversal → reject absolutes, normalize-before-check.
- **HIGH SSRF**: `url_validator` host extraction kept `user@` userinfo
  (`http://evil.com@trusted.com`) and accepted `%`-encoded hosts → strip userinfo, reject `%`.
- **HIGH log-forging**: audit-log embedded raw user fields → CRLF sanitization.
- `prompt_sanitizer` delimiter-injection strip.

### Auth / KMS / secrets
- SDN credential lookup prefix-confusion (`FOO` matched `FOOBAR`) → exact-key boundary.
- Bearer-token header injection (whitespace/newline) rejected.
- KMS request fields JSON-escaped; key-handle values masked in `export_sdn`.
- Redis session-key/encoding injection chars rejected.

## REVERTED — kernel changes (build-breaking and/or arch-level; NOT applied)

The kernel agent found real, severe holes but its patch introduced build breaks and
changed kernel boot semantics. Reverted all 6 files pending your decision.

### Real kernel holes found (need fixing — see ESCALATE)
- **CRITICAL uninitialized = god-mode**: `CapabilitySet.full()` (empty caps) means
  "all rights"; `_ensure_record()` auto-creates unknown tasks with `full()`. A task
  acting before explicit init briefly holds unrestricted authority.
- **CRITICAL baremetal BSS-zero**: module-level `val` constants (ARM MPU addresses,
  rights masks, PRIVCTL op-codes) are 0 after BSS clear on baremetal LLVM → MPU writes
  to address 0, sandbox silently not applied; `_rights_allow(0,0)` returned `true`.
- **HIGH cap-generation forgery**: `_handle_cap_grant` copied user `arg2` into
  `CapabilityToken.generation` → stale-token replay.
- **HIGH**: `_handle_debug_write` ungated (covert channel / audit bypass).
- **HIGH**: `cap_init_task_record(task, full:true)` accepted `full` for any task id.

### Why reverted (defects in the patch)
- `sched.get_privilege_mask(current)` — **no such method exists** in `src/os` (build break).
- Renamed `_handle_debug_write` → `_impl` but 3 importers still use the old name
  (`syscall.spl:67/488`, `syscall_shim.spl`, `syscall_shim_process.spl`) (build break).
- Default capability grant `full → deny-all` in `_ensure_record` + pid-1-only
  `cap_init_task_record` change **kernel boot semantics** — arch decision.

## ESCALATE — architecture decisions (need user approval)

1. **Kernel capability default model**: flip `_ensure_record` / `cap_init_task_record`
   to default-deny (deny-all on uninit, full only for pid 1). Requires task-lifecycle
   audit (spawn/exec must explicitly grant) — could affect boot. **Highest value.**
2. **Capability unforgeability**: make `CapabilityToken.generation` kernel-assigned
   (ignore user `arg2`); document `arg2` as reserved. Syscall ABI doc change.
3. **Debug syscall gating**: gate `_handle_debug_write` behind a privilege mask; needs a
   `Scheduler.get_privilege_mask` method + dispatch-table rewire.
4. **Baremetal security constants**: convert all kernel security-critical `val`
   constants to function-local literals (BSS-zero-safe) + fail-closed sandbox-boot gates.
5. **AOP runtime/compile-time proceed mismatch**: `Around` runtime advice has no real
   `proceed()`; compile-time layer does. Reconciling needs an `Advice.handler` contract change.
6. **AOP registry access control**: `get_registry()` is `pub`, returns mutable registry —
   any module can `disable_unsafe()`/`unregister_unsafe("auth")`. Needs capability-gated
   or trusted-init-only access (module access-control decision).
7. **Security-aspect priority band**: user advice can register at priority > security
   aspects and run first. Needs a reserved priority band enforced by the compiler.
8. **SecurityContext entry validation**: `gate.check_capability` trusts `ctx.capabilities`
   strings; validate entries at construction or restrict population to trusted paths.
9. **secure_random (.smf, compiled)**: could not audit CSPRNG seeding source — verify
   `getrandom`/`/dev/urandom` vs weak entropy in the `.spl`/Rust source.

## Lower-risk follow-ups (no approval needed; deferred)
- CORS `Vary: Origin` injection (response-serialization layer).
- CSRF empty-`secret_key` startup validation.
- Rate-limit trusted-proxy XFF policy as first-class config.
- Reuse canonical `constant_time_compare` instead of per-module copies.
