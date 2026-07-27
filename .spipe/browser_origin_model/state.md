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

## 3. Spec — `test/01_unit/browser_engine/security/origin_model_spec.spl`

8 describe blocks, **122 examples, 0 failures**, byte-identical verdicts on
`bin/simple run` (JIT) and `SIMPLE_EXECUTION_MODE=interpreter`:

| block | examples |
|---|---|
| origin derivation is fail-closed | 15 |
| same-origin equality is a strict tuple comparison | 9 |
| opaque origins trust nothing | 9 |
| same-origin policy decision points | 15 |
| cookie admission enforces the attribute rules | 20 |
| cookie delivery honours domain, path, Secure and SameSite | 26 |
| permissions are default-deny and origin-scoped | 21 |
| deliberate-red calibration proves the oracles bite | 7 |

### Deliberate-red calibrations (source really broken, then reverted)

| # | injected breach | result |
|---|---|---|
| RED 1 | `same_origin` reduced to `left.host == right.host` | **6 reds**: `denies http://x:80 vs https://x:443`, `denies ws vs http…`, `denies two ports…`, `denies access across a scheme change…`, and both equality calibrations |
| RED 2 | `is_public_suffix` rejection deleted from `validate_set_cookie` | **4 reds**: `rejects Domain=com`, `rejects Domain=co.uk`, `rejects a dot-prefixed public suffix`, and the public-suffix calibration |
| RED 3 | `PermissionSet.query` default flipped to `Granted` | **10 reds** across default-deny, every cross-origin/scheme/port/subdomain leak case, revoke, `revoke_origin`, and the default-deny calibration |

Each red was reverted from a byte-for-byte backup under `build/brorigin_*.bak`
and the suite re-verified green on both engines afterwards.

Note on spec authoring: describe-level `val` fixtures are NOT reliably visible
inside every `it` body on this runner (10 examples failed with
`semantic: variable 'secure_origin' not found` while sibling examples in the
same context resolved it). Fixtures are module-level functions instead.

## 3b. Regression A/B on the touched shared entity

Adding `expires_at` to `Cookie` required updating all 11 existing literal
construction sites (a struct literal that OMITS a defaulted field is nil-filled
to `3` on the JIT — probe `build/brorigin_probe/defaults.spl` prints `b=3` under
`bin/simple run` and `b=7` under the interpreter — which would have made every
existing cookie look expired at unix 3).

`test/01_unit/browser_engine/net/cookie_store_spec.spl` reports **22 examples,
2 failures** both before and after the change (A/B'd by restoring the three
files from `HEAD` and re-running): identical failures
`AC-6: stored cookie is returned for matching request` and
`AC-6: newer cookie with same name replaces older one`. **Pre-existing, not
caused by this lane.** Root cause looks like the multi-hop mutation landmine:
`CookieStore.store` does `val jar = self._jars[idx]` then `jar.add(c)` — the
extracted array element is mutated without being written back.

## 3c. Lint

`bin/simple lint src/lib/gc_async_mut/gpu/browser_engine/security/` reports
`COLL006 string concat in loop` on functions that contain no concatenation at
all (`_parse_port`, `_cut_at_delims`, `_is_scheme_token`, `_is_host_token`,
`is_known_feature`). This is ambient false-positive noise, not a defect
introduced here: the same rule fires on the untouched peers
`src/lib/common/web/public_suffix.spl:7` (`_public_suffix_text_less`, also
concat-free) and `src/lib/gc_async_mut/gpu/browser_engine/net/cookie_store.spl:13`.
`primitive_api` fires on `now: i64` timestamps; introducing a newtype for a
unix-seconds clock value would be over-engineering against the tree's
conventions. `non_exhaustive_match` fires on matches that DO cover every enum
variant; adding an unreachable catch-all would be dead code.

## 4. Explicitly still BLOCKED (do not read this lane as Phase 7 done)
- renderer / network / GPU **process split** and site isolation — multi-session, needs
  the OS process + IPC lanes; the model here is enforcement *logic*, not a sandbox.
- **Wiring into a live renderer**: `dom.spl` / `script/*` / `resource_loader.spl` still
  do not consult these decision points. Out of scope for this lane by instruction.
- WPT / Test262 conformance — external corpora absent.
