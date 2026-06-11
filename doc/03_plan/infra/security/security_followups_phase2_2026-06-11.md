# Security Hardening — Phase 2 Follow-ups Plan (2026-06-11)

Continuation of the 2026-06-11 parallel security audit. Phase 1 (fail-open →
fail-closed across AOP, capability, web, sanitizers, secrets, kernel) is landed
and pushed in `main`. This plan decomposes the remaining ESCALATE/follow-up items
into small, parallelizable tasks.

Numbering follows the orchestrator's status list:

| # | Item | Disposition |
|---|------|-------------|
| 1 | Build + QEMU kernel boot verification | **POSTPONED** until E0410 refactor unblocks a clean build |
| 2 | AOP runtime `Around` `proceed()` contract | **PLAN / ARCH-GATED** — design only, needs user go/no-go |
| 3 | `secure_random` CSPRNG seeding audit | **IMPLEMENT** (audit + fix if weak) |
| 4 | Lower-risk web follow-ups (4a–4d) | **IMPLEMENT** (parallel) |

Execution model: Sonnet implementer agents on **disjoint file scopes**, Opus
(orchestrator) review + commit, **Fable final review** with fix-forward, then
doc/guide/spipe-skill update.

---

## Item 1 — POSTPONED

`bin/simple build` / QEMU SimpleOS boot is not runnable cleanly while the repo is
mid-E0410 export refactor and parallel agents are mutating `src/`. The kernel
changes (default-deny caps, fail-closed sandbox boot) are statically
symbol-verified and pushed. **Re-open when:** `git log` shows the E0410 sweep
complete and `bin/simple build` returns clean; then run
`sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke` and the SimpleOS boot
path. Tracked as the single blocking validation gap.

---

## Item 2 — AOP runtime `Around` `proceed()` contract (ARCH-GATED, design only)

### Problem
`src/lib/nogc_sync_mut/src/aop.spl` runtime weaver treats `Around` advice as a
*pre-hook*: `AspectWeaver.wrap` runs the Around handler before `func()` with no
way to (a) wrap the call, (b) short-circuit it, or (c) observe/transform the
result. The compile-time MDSOC layer (`src/compiler/85.mdsoc`,
`aop_support_matrix.sdn: proceed: exactly_once`) *does* model a real `proceed`.
The two layers disagree — a security `Around` advice (e.g. output sanitization,
audit-wrap) that relies on `proceed()` behaves correctly when woven at compile
time but silently degrades to a fire-and-forget pre-hook at runtime.

### Why this is an architecture decision
The fix changes the `Advice.handler` contract. Current:
```
struct Advice:
    kind: AdviceKind
    handler: fn(AdviceContext) -> Result<(), text>
```
A real `Around` needs the handler to receive a continuation it can call:
`fn(AdviceContext, proceed: fn() -> Result<T, text>) -> Result<T, text>`. That is
generic over the join-point return type `T`, which the current non-generic
`Advice` struct cannot hold. This ripples into `AspectRegistry`,
`register_aspect`, and every advice author.

### Design options (for user decision)
- **Option A — Separate Around handler field (recommended).** Keep
  `handler: fn(AdviceContext) -> Result<(), text>` for Before/After/AfterError.
  Add `around_handler: fn(AroundContext) -> Result<Any, text>?` where
  `AroundContext` carries a `proceed: fn() -> Result<Any, text>` thunk. `wrap<T>`
  builds the proceed thunk closing over `func`. Pros: Before/After advice and all
  existing callers unchanged; additive. Cons: `Any` boxing at the proceed
  boundary (Simple has no per-aspect generics in a struct field).
- **Option B — Make `Advice`/registry generic over `T`.** Cleanest typing, but
  `AspectRegistry.aspects: [Aspect]` becomes heterogeneous-impossible without
  boxing anyway; rejected (registry holds mixed join points).
- **Option C — Document-and-restrict.** Forbid runtime-registered `Around`
  security advice; require security `Around` to be compile-time woven only.
  Cheapest; codifies current reality. Loses runtime flexibility.

### Recommendation
Option A, behind a Fable design review, then user go/no-go before any code lands.
**No implementation in this phase.** Closure-capture limits (Simple nested
closures can read but not mutate outer vars — `.claude/rules/language.md`) must be
validated against the proceed-thunk approach before commitment.

### Deliverable this phase
This design section + a Fable review note. No `aop.spl` edit.

---

## Item 3 — `secure_random` CSPRNG seeding audit (IMPLEMENT)

### Scope (disjoint, audit-first)
- `src/lib/nogc_sync_mut/src/core/random.spl`
- `src/lib/nogc_sync_mut/io/crypto_sffi.spl`
- `src/lib/common/random_pure.spl`
- `src/runtime/runtime.c` (read the `rt_*` random extern only — vendored/runtime,
  do not refactor)

### Task
Trace the entropy source feeding any function named `secure_*`/`*_secure`/token
generation. Confirm it routes to an OS CSPRNG (`getrandom(2)` / `/dev/urandom` /
`arc4random`) and **not** a seeded LCG/xorshift (`random_pure.spl`). If a
security-sensitive path (CSRF token, session id, key/nonce) uses the non-CSPRNG
`random_pure` generator, redirect it to the CSPRNG extern (fail-closed: error if
the CSPRNG extern is unavailable rather than falling back to weak PRNG).
Deliver: a 10-line findings note + a fix only if a weak path is confirmed.

---

## Item 4 — Lower-risk web follow-ups (IMPLEMENT, parallel)

Each sub-item is one disjoint file. No approval needed.

### 4a — CORS `Vary: Origin` (file: `http_server/cors.spl`)
When the response reflects a specific request Origin (not literal `*`), caches
must vary on Origin or a shared cache can serve one origin's allowed response to
another. Add `Vary: Origin` to `build_cors_headers` and `handle_preflight`
whenever the emitted `Access-Control-Allow-Origin` is a reflected origin (skip
when it is the literal `*`).

### 4b + 4d — CSRF empty-secret + constant-time dedup (file: `http_server/csrf.spl`)
- **4b:** `CsrfConfig.default()` ships `secret_key: ""`. `csrf_handler` and both
  `generate_csrf_token*` must fail closed when `secret_key == ""`: return a
  deny/`Error` (never validate or mint a token under an empty key). An empty HMAC
  key produces forgeable tokens.
- **4d:** Replace the private `constant_time_eq` (csrf.spl:187) with the canonical
  `constant_time_compare` from `src/lib/common/crypto/constant_time.spl` (import
  and delegate; keep a thin local alias only if the import path forces it). Leave
  the `tls/` copies for a separate pass (different module, out of scope).

### 4c — Rate-limit trusted-proxy XFF (file: `http_server/rate_limit.spl`)
Rate-limit keying currently uses `peer_addr`. If a future change keys on
`X-Forwarded-For` naively, any client spoofs the header to evade limits. Add a
`trusted_proxies: [text]` config field (default `[]`). Only consult
`X-Forwarded-For` when the direct `peer_addr` is in `trusted_proxies`; otherwise
always key on `peer_addr`. Default behavior unchanged (empty list ⇒ peer_addr).

---

## Parallelization map

| Agent | Model | File scope | Commit? |
|-------|-------|-----------|---------|
| A-cors | Sonnet | `http_server/cors.spl` | no (orchestrator commits) |
| A-csrf | Sonnet | `http_server/csrf.spl` | no |
| A-ratelimit | Sonnet | `http_server/rate_limit.spl` | no |
| A-random | Sonnet | random/crypto_sffi (audit) | no |
| Review-1 | Opus | all diffs | commits after review |
| Final | **Fable** | combined diff + item-2 design | fix-forward |
| Docs | Sonnet | guide + spipe skill (disjoint from code) | no |

Item 2 design authored by orchestrator (Opus); no code edit.

## Doc / guide / spipe-skill update
- `doc/07_guide/infra/webapp_security.md` — Vary:Origin, empty-secret fail-close,
  XFF trusted-proxy, canonical constant-time.
- `doc/07_guide/lib/misc/security.md` — secure_random CSPRNG guidance.
- spipe security skill / spec — add Phase-2 regression notes (sdoctest-backed
  where runnable; documented otherwise).
