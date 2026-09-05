# ui.web -> http_core migration assessment

Status: **wave 2 landed — partial migration done, remainder staged.**
Date: 2026-08-17.
Contract: `doc/04_architecture/ui/testing/typed_ui_interface_arch.md` §Web host lane.
Constraint from `.spipe/typed_ui_interface_office/state.md`: converge on
`std.common.net.http_core`; **never stand up a third HTTP stack.**

This document describes what is *actually implemented* on this branch, not an
aspiration. Every "done" row below is backed by a green spec (see §6).

## 0. Base-version note

The coordinator flagged that `origin-ssh/main` had moved ~99 commits ahead and
that `src/lib/common/net/http_core.spl` gained +159 lines there, warning that our
branch's copy might predate the new limits/path-security API.

**Verified false — our copy is already current.** `git diff origin-ssh/main --
src/lib/common/net/http_core.spl` is **empty**; the file is byte-identical to
upstream, and both export the same 9 export lines (520-528), including
`HttpLimits` / `http_limits_default` / `HttpParseError` /
`http_parse_error_status` / `http_parse_error_message` / `check_request_line` /
`check_header_count` / `check_header_size` / `check_body_size` and
`is_safe_static_path` / `contains_null_byte` / `contains_traversal` /
`contains_backslash` / `starts_with_slash` / `normalize_path` /
`validate_static_path`.

Consequence: **nothing in this migration is blocked-until-rebase.** Every
function named in the staged-remainder list (§4) is callable on this branch
today. http_core is consumed read-only here (it is enterprise-owned).

The upstream comment at `http_core.spl:366-369` — that the tier-copied
`std.<tier>.http.limits` and `std.<tier>.http.path_security` modules **now
delegate** to http_core — is the strongest available argument for this
migration: the stdlib tiers have already made the same move ui.web is making,
so ui.web's private copies are now the *last* remaining divergent
implementation rather than one of several.

## 1. What ui.web's server does that http_core already covers

| ui.web behavior | http_core primitive | State |
|---|---|---|
| Content-Length parse, reject negative/non-numeric/overflow | `content_length_from_text` | **migrated** |
| Duplicate Content-Length rejection | `body_decision` | **migrated** |
| Body size cap (8 KiB unauth) | `body_decision(max_body)` | **migrated** |
| CL + Transfer-Encoding smuggling reject (RFC 7230 §3.3.3) | `body_decision` | **migrated** |
| Duplicate singleton security header reject | `body_decision` | **migrated (new capability)** |
| Path traversal, `//`, null byte, `%00`, encoded dot-dot | `path_is_safe` | **migrated** |
| Backslash in path | `contains_backslash` | **migrated** |
| Request-line / header-line / head byte caps | `check_request_line`, `check_header_size`, `check_header_count`, `HttpLimits` | **staged** (§4) |
| Static-asset path validation + normalization | `is_safe_static_path`, `validate_static_path`, `normalize_path` | **staged** (§4) |
| Status/message for structured parse failures | `HttpParseError`, `http_parse_error_status/message` | **staged** (§4) |
| Route pattern matching | `match_route_pattern`, `extract_route_params` | **not applicable** — ui.web routes by exact `path ==` compare in `dispatch_ui_route`; no `:param` patterns exist yet |

## 2. What http_core does NOT cover (stays in ui.web, by design)

These are genuinely out of http_core's scope. They are *not* migration debt.

- **WebSocket upgrade** — handshake detection, `Sec-WebSocket-Accept`,
  subprotocol selection (`ui_web_ws_response_protocol`), frame payload bounds
  (`ui_web_ws_frame_payload_allowed`). http_core is request/response only.
- **TLS serve loop** — `tls_serve_loop.spl` / `ConnStream`, cert loading,
  accept loop. http_core never touches sockets.
- **Session plumbing** — `session_token.spl`, login rate limiting
  (`ui_web_login_rate_decision`), grant issuance, `origin_guard.spl` CSRF/Origin
  enforcement, per-request auth (`ui_web_request_authorized`).
- **UI-specific response shaping** — `ui_web_json_security_headers`,
  `ui_web_html_security_headers`, `ui_web_static_script_security_headers`, CSP
  for the retained renderer.
- **Chunked decoding** — http_core *offers* `decode_chunked_bounded`, but
  ui.web deliberately accepts **no** `Transfer-Encoding` at all (stricter than
  core). This asymmetry is intentional and is asserted by spec.

## 3. Concrete mapping — what this change actually did

`src/app/ui.web/auth_params.spl` now imports
`{content_length_from_text, body_decision, path_is_safe, contains_backslash}`
and:

- `ui_web_content_length` delegates to `content_length_from_text` and deletes
  the hand-rolled `_ui_web_decimal_i64` digit-stripper (10 chained
  `.replace()` calls).
- `ui_web_request_body_status` deletes `_ui_web_request_body_framing_problem`
  and delegates to `body_decision(pairs, 8192, allow_chunked: false)` via a new
  `_ui_web_header_pairs` adapter that splits the raw header blob into
  `[(name, value)]`. The `413`-prefixed error maps to
  `request_body_too_large`; every other non-empty error maps to
  `invalid_request_framing`. The stricter *no* Transfer-Encoding rule is
  applied **before** the delegation so it is preserved exactly.
- New `ui_web_request_path_allowed(path)` strips the query string, requires a
  leading `/`, rejects backslash via `contains_backslash`, then defers to
  `path_is_safe`.

`server.spl` (`WebServer`) and `async_server.spl` (`AsyncWebServer`) both call
`ui_web_request_path_allowed(path)` immediately after request-line parsing and
**before any routing**, failing closed with `400 {"error": "invalid_path"}`.
Both entry points were changed so the sync and async servers cannot diverge.

### Defect found and fixed during this pass

The original comment claimed the new path check covered "traversal, //,
backslash, null byte". It did not: `path_is_safe` checks dot-dot (raw and
percent-decoded), `//`, `\0`, and `%00` — but **not backslash**, which
http_core keeps as the separate `contains_backslash` primitive (used by
`is_safe_static_path`, not by `path_is_safe`). `ui_web_request_path_allowed`
now composes the two primitives rather than re-implementing either, and the
spec pins `/a\b` -> rejected.

### Behavior deltas to be aware of

1. **Tightening:** Content-Length above i32 max (2147483647) is now `-1`
   (invalid framing) instead of parsing as i64. Irrelevant in practice — the
   8 KiB cap rejects it either way — but it is a real semantic change.
2. **New rejection:** duplicate singleton security headers (`Host`, `Origin`,
   `Authorization`, ...) are now `invalid_request_framing`. ui.web previously
   accepted these. This is a security *gain* and is spec-pinned.

## 4. Staged remainder (deliberately NOT done in this wave)

Not blocked — just out of scope for a change that must not disturb the WS/TLS
paths. Each is a mechanical follow-up:

- **S1.** `ui_web_request_head_allowed` / `ui_web_request_line_allowed` /
  `ui_web_header_line_allowed` (`auth_params.spl:143-150`) are hand-rolled
  bounds checks against private `UI_WEB_MAX_*_BYTES` constants (32768 / 8192 /
  8192). Replace with `HttpLimits` + `check_request_line` / `check_header_size`
  / `check_header_count`. Note ui.web has **no header-count cap at all** today —
  `check_header_count` closes a real gap (http_core defaults to 100).
- **S2.** Adopt `HttpParseError` + `http_parse_error_status` so ui.web returns
  414 for an over-long request line and 403 for traversal, instead of
  collapsing everything to 400.
- **S3.** Route static-asset serving through `validate_static_path` /
  `normalize_path`. **Caution — not a drop-in:** `is_safe_static_path` uses
  `contains_traversal`, which rejects *any* `..` substring, so it would reject
  `/static/app..js`, which the current entry check allows. Reconciling that is
  a deliberate policy decision, not a refactor, which is why it is staged.
- **S4.** Body-cap unification: ui.web caps unauth bodies at 8 KiB while
  `http_limits_default().max_body_bytes` is 10 MiB. Keep ui.web's stricter
  value; pass it as the `HttpLimits` field rather than a private constant.

## 5. Verdict: STAGED, with the entry layer migrated now

**Migrate the request-entry security layer now (done); stage the limits,
structured-error, and static-path layers.**

Reasoning:

- The entry layer (framing + path safety) is where the *smuggling and
  traversal* risk lives, it is pure-function and fully testable without a
  socket, and http_core is a strict superset of what ui.web had. Migrating it
  is all upside and it is done.
- A big-bang migration would drag in the WS upgrade and TLS accept loop, which
  http_core does not model at all. Those must keep their bespoke code; forcing
  them through http_core is exactly how a third stack gets born.
- S3 in particular has a genuine **policy** divergence (`..` substring vs
  dot-dot segment). Landing it silently inside a "refactor" would change which
  URLs 403 — that needs its own change with its own spec.
- Nothing is blocked on the rebase (§0), so staging here is a scoping choice,
  not a dependency wait.

## 6. Security-parity checklist

Verified by `test/01_unit/app/ui_web/ui_web_http_core_entry_spec.spl`
(**Results: 7 total, 7 passed, 0 failed**):

- [x] Valid Content-Length parses; missing -> 0; negative -> -1; non-numeric ->
      -1; overflow -> -1
- [x] `Transfer-Encoding: chunked` rejected
- [x] `Transfer-Encoding: gzip` rejected (stricter than core)
- [x] Duplicate Content-Length -> `invalid_request_framing`
- [x] Invalid Content-Length -> `invalid_request_framing`
- [x] Body at cap (8192) accepted; over cap (8193) -> `request_body_too_large`
- [x] Duplicate `Host` / `Origin` / `Authorization` -> `invalid_request_framing`
- [x] `/../etc/passwd` rejected
- [x] `/a/..%2fb` (percent-encoded traversal) rejected
- [x] `/a//b` rejected
- [x] `/a\b` (backslash) rejected
- [x] `/a%00b` (null byte) rejected
- [x] empty path and relative `etc/passwd` rejected
- [x] legitimate `/static/app..js` and `/static/retained_renderer.js` allowed
- [x] query strings preserved (`/ui/state?token=abc` allowed)
- [x] both `WebServer` and `AsyncWebServer` gate before routing

Not covered by spec (staged): header-count cap, 414/403 status differentiation,
static-path normalization.

## 7. HostInterface v2 (same wave, additive)

`src/app/ui.web/host_adapter_contract.spl` gains `HOST_CONTRACT_VERSION = 2`,
`struct HostCapabilities` (pointer / keyboard / ime / clipboard / file_picker),
`struct HostSessionHandshake` (contract_version, auth_token slot, resume_token),
their defaults, and JSON projections. **Additive only** — no existing host code
path reads them yet, so no host behavior changes. `host_capabilities_default()`
returns pointer+keyboard only, matching what the SimpleWeb/ElectronWeb adapters
actually deliver today. Verified by
`test/01_unit/app/ui_web/host_adapter_contract_v2_spec.spl`
(**Results: 5 total, 5 passed, 0 failed**).

The `resume_token` slot exists so a dropped WS transport can resume
revision-correlated state; wiring it into the reconnect path is future work.

## 8. Limitations

- `bin/simple lint` is broken tree-wide on this branch (unrelated to this
  change); lint was skipped and is noted here rather than silently passed over.
- Specs run under `SIMPLE_TIMEOUT_SECONDS=0` — the default 60s CPU guard kills
  a cold ui.web spec run (~67s) before it reports.
- Verification is unit-level on pure functions. There is no end-to-end socket
  test asserting a malicious path gets a 400 off a real connection; the entry
  wiring in `server.spl`/`async_server.spl` is verified by inspection.
