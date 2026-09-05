# browser_origin_model — lane BRORIGIN

Roadmap Phase 7, security-model slice. Phase 7's other halves (renderer/network/GPU
process split, WPT/Test262 conformance) stay blocked — they need multi-session work
and external corpora respectively. The origin/cookie/permission model is pure logic
and is implementable + testable here.

## 1. Survey (written BEFORE implementation)

### Where the browser tree lives
- Engine: `src/lib/gc_async_mut/gpu/browser_engine/` (129 `.spl` files) — Chromium-mirrored
  naming (`dom.spl`, `layout*.spl`, `paint.spl`, `net/`, `script/`, `js/`).
- Blink-named subset: `src/lib/blink/{dom,css_parser}`.
- Host embedders: `src/os/hosted/hosted_browser_renderer_policy.spl`,
  `src/os/hosted/hosted_web_content_session.spl` (NOT ours to edit; they consume `Origin`).

### What already EXISTED (reuse, do not duplicate — master plan §4 no-second-envelope)
| Concept | Where | State |
|---|---|---|
| `Url` (scheme/host/port/path/query/fragment) + `parse` | `net/entity/url_types.spl` | complete enough |
| `Origin` (scheme, host, port) + `from_url` + `to_text` | `net/entity/url_types.spl` | **tuple only** — no equality, no opaque, no policy |
| `Cookie` (name/value/domain/path/secure/http_only/same_site) | `net/entity/cookie_types.spl` | **no expiry**, attributes are inert data |
| `SameSite {Strict,Lax,None}` | `net/entity/cookie_types.spl` | enum only, no semantics |
| `parse_set_cookie`, `CookieJar`, `CookieStore` (domain/path match, per-domain cap) | `net/cookie_store.spl` | matching exists but **accepts any domain** — no public-suffix guard, no Secure/SameSite validation, no origin binding |
| `is_public_suffix(domain)` + PSL data | `src/lib/common/web/public_suffix.spl`, `public_suffix_data.spl` | complete, **unused by the cookie store** |
| CORS preflight | `net/cors.spl` | uses `Origin`, string-compares `to_text()` |

### What was MISSING (the production-blocking gap the ledger names)
1. No origin **equality** — `Origin` had no `same_origin`; CORS compared serialized text,
   which cannot express opaque origins at all.
2. No **opaque / unique origin** — `data:`, sandboxed iframes, and unparseable URLs all
   fell through to a `("", "", 0)` origin that compared **equal to every other broken
   origin**. That is a same-origin breach by construction.
3. No **same-origin policy decision points** — nothing decided document access, storage
   partitioning, or network read access; there was no fail-closed path for unparseable input.
4. Cookie attributes were **parsed but never enforced**: `Secure` ignored on insecure
   schemes, `SameSite=None` accepted without `Secure`, `Domain=com` accepted (public-suffix
   cookie-injection pitfall), no expiry field at all.
5. **No permission model anywhere in the browser tree** (`grep -rl permission` over the
   engine tree: zero hits).

### Decision: extend, don't fork
- Keep `Origin` in `net/entity/url_types.spl` as THE origin type. Opaque origins are
  encoded inside it (`scheme = "null"`, `host` = unforgeable nonce, `port = -1`) so no
  second origin envelope appears and `net/cors.spl` / `src/os/hosted/**` keep compiling.
- Keep `Cookie`/`SameSite` in `net/entity/cookie_types.spl`; add only `expires_at: i64`
  (defaulted, so the 13 existing literal construction sites stay valid).
- Reuse `common.web.public_suffix.is_public_suffix` rather than adding a suffix list.
- New policy code lives in `browser_engine/security/` and operates on those existing types.

## 2. Model shape (implemented)

`src/lib/gc_async_mut/gpu/browser_engine/security/origin_policy.spl`
- `opaque_origin(nonce)` / `is_opaque(o)` / `origin_from_url_text(raw)` (fail-closed:
  anything unparseable, non-hierarchical, or `data:`/`blob:`/`javascript:`/`about:`
  becomes a *fresh* opaque origin).
- `same_origin(a, b)` — tuple equality on (scheme, host, port); opaque is same-origin
  only with the *identical* opaque origin (nonce match), never with a re-derived one.
- `serialize_origin(o)` — `"null"` for opaque, `scheme://host[:port]` otherwise, default
  ports elided.
- Decision points, all **deny-wins / fail-closed**:
  `can_access_document`, `storage_key` + `can_use_storage`, `can_read_response`.

`src/lib/gc_async_mut/gpu/browser_engine/security/cookie_policy.spl`
- `validate_set_cookie(cookie, origin, now)` → `CookieVerdict{accepted, reason}`.
  Rejects: empty name; `SameSite=None` without `Secure`; `Secure` from a non-secure
  origin; `Domain` that is a public suffix; `Domain` not domain-matching the request
  host; already-expired.
- `cookie_applies(cookie, origin, request_path, is_same_site_request, is_top_level_nav, now)`
  — Secure-channel check, domain match, path match, expiry, and SameSite
  (Strict = same-site only; Lax = same-site or top-level navigation; None = any, but
  only reachable once `validate_set_cookie` forced `Secure`).
- `script_visible(cookie)` — HttpOnly cookies are never returned to script.

`src/lib/gc_async_mut/gpu/browser_engine/security/permission_policy.spl`
- `PermissionState {Denied, Granted}` with **Denied as the default for every query**.
- `PermissionSet` keyed by `serialize_origin(origin) + "|" + feature`; `grant`, `revoke`,
  `query`. `grant` on an opaque origin is a silent no-op — an opaque origin can never
  hold a grant, so a revoked or foreign origin can never observe `Granted`.

## 3. Spec

`test/01_unit/browser_engine/security/origin_model_spec.spl` — adversarial matrix
(cross-origin document access, scheme/port distinctness, opaque non-identity,
`SameSite=None` without Secure, `Domain=com`, permission leak/revoke) plus two
deliberate-red calibrations.

## 4. Explicitly still BLOCKED (do not read this lane as Phase 7 done)
- renderer / network / GPU **process split** and site isolation — multi-session, needs
  the OS process + IPC lanes; the model here is enforcement *logic*, not a sandbox.
- **Wiring into a live renderer**: `dom.spl` / `script/*` / `resource_loader.spl` still
  do not consult these decision points. Out of scope for this lane by instruction.
- WPT / Test262 conformance — external corpora absent.
