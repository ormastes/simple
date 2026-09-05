# Lane BRWIRE — browser enforcement wiring

Goal: make `security/{origin_policy,cookie_policy,permission_policy}.spl` the ONE
owner of every same-origin / cookie / permission decision in the browser engine.
BRORIGIN built the model; nothing called it.

## Baseline (before any edit, 2026-07-27)

| spec | JIT | interpreter |
|---|---|---|
| `test/01_unit/browser_engine/net/cors_spec.spl` | 6/6, 6/6, 4/4, 12/12 — 0 fail | (same) |
| `test/01_unit/browser_engine/net/cookie_store_spec.spl` | 9/9, 4/4, 4/4, **5 ex / 2 fail** | (same) |
| `test/01_unit/browser_engine/security/origin_model_spec.spl` | 7 green describes, **20 ex / 10 fail** | identical |

Both pre-existing reds are NOT model bugs:
- `origin_model_spec` 10 fails = `semantic: variable 'secure_origin' not found` —
  the documented describe-level-`val`-not-captured-in-`it` landmine, in BRORIGIN's
  read-only spec. Identical on both engines. Not mine to edit.
- `cookie_store_spec` 2 fails = `CookieStore.store` extract-mutate-without-write-back
  (`val jar = self._jars[idx]` then `jar.add(c)`), as BRORIGIN predicted.

## Survey — every origin/cookie/permission decision point

| # | site | decision | BEFORE | AFTER |
|---|---|---|---|---|
| 1 | `net/cors.spl` `needs_preflight(req, origin)` | same-origin | hand-rolled `scheme==  and host== and port==` triple compare on raw `Url` fields | `origin_policy.same_origin` |
| 2 | `net/cors.spl` `CorsChecker.is_same_origin` | same-origin | `self._origin == cors_url_origin(url)` — serialized-origin **string compare**; `""` origin special-cased | `origin_policy.same_origin` on derived `Origin`s |
| 3 | `net/cors.spl` `cors_url_origin(url)` | origin serialization | own re-implementation of default-port elision | **DELETED** → `origin_policy.serialize_origin` |
| 4 | `net/cors.spl` `validate_response` | response readability | ad-hoc: `""`→deny, `*`+creds→deny, `allowed==self._origin` string compare. Accepts literal `Access-Control-Allow-Origin: null`; accepts a grant to a malformed requester | `origin_policy.can_read_response` |
| 5 | `net/cookie_store.spl` `get_header(host, path)` | cookie attachment | domain+path only. **`Secure`, `HttpOnly`, `SameSite`, expiry all ignored** — a `Secure` cookie was attached over `http:` | **DELETED**; replaced by `get_header_for_origin(...)` → `cookie_policy.cookie_applies` |
| 6 | `net/cookie_store.spl` — script read of cookies | `HttpOnly` visibility | **did not exist** — no script surface, and `get_header` would have leaked `HttpOnly` | `script_cookie_header(...)` → `cookie_policy.script_visible` + `cookie_applies` |
| 7 | `net/cookie_store.spl` `store(c)` | Set-Cookie admission | stored anything `parse_set_cookie` produced; no origin, no validation | `store_from_origin(...)` → `cookie_policy.validate_set_cookie`; jar key from `effective_domain` |
| 8 | `script/storage_api.spl` | storage partitioning | one global `BrowserStorage`; no origin, no key | `PartitionedStorage` → `origin_policy.storage_key` / `same_storage_partition`; opaque origin gets `""` = no storage |
| 9 | cross-document access | `can_access_document` | **did not exist** — `dom.spl` has no document/origin notion at all, so nothing was checked | new `browsing_context.spl`: every document read goes through `origin_policy.can_access_document` |
| 10 | response body read by script | `can_read_response` | **did not exist** at any call site | `browsing_context.read_response(...)` |
| 11 | `script/clipboard_api.spl` read/write | permission gate | ungated `clip._text` read/write | gated via `browsing_context` + `PermissionSet.allows("clipboard-read"/"clipboard-write")` |
| 12 | `script/navigator_api.spl` powerful features | permission gate | `secure_context: bool` flag only, no per-origin grant | `browsing_context.call_gated(...)` default-deny |
| 13 | `resource_loader.spl` | — | pure Content-Type sniffing, `ResourceLoader` is a stub with `_fetch: text` | left alone; the loader has no origin to enforce on. Enforcement for loads lives at #10. Recorded as model-only. |

Ad-hoc comparisons deleted: #3 `cors_url_origin`, #2 string-equality same-origin,
#1 triple-field compare, #4 hand-rolled ACAO matching, #5 unconditional attachment.

## Deliberate-red calibration
See `## Red log` below.

## Red log

### Red 1 — `can_read_response` neutered
Patched `browsing_context.read_response` to return the body unconditionally
(ignoring `can_read_response`).
Result: `enforcement_spec.spl` describe "response reads are gated by CORS"
went **5 examples, 4 failures** (was 5/0). Reverted → 5/0 green again.

### Red 2 — `cookie_applies` bypassed on attachment
Patched `CookieStore.get_header_for_origin` to skip `cookie_applies` and attach
every domain/path match (i.e. restored the pre-wiring behaviour).
Result: describe "cookie attachment is gated by the cookie policy"
went **6 examples, 4 failures** (was 6/0). Reverted → 6/0 green.

### Red 3 — storage partition key collapsed
Patched `PartitionedStorage._key` to return a constant.
Result: describe "storage is partitioned per origin" went
**5 examples, 3 failures** (was 5/0). Reverted → 5/0 green.

### Red 4 — `can_access_document` neutered (session 2)
Patched `BrowsingContext.can_access` to `return true` once the document exists,
i.e. dropped the origin check entirely while keeping the "unknown document"
guard — the exact shape of the bug this lane exists to prevent.
Log: `build/brwire_2/red4_can_access.log`.
Result: **46 total, 41 passed, 5 failed** —
`cross-document access is refused at the call site` **7 ex / 4 fail**, and
`an opaque origin gets nothing` **9 ex / 1 fail** (the opaque-reads-another-
document example). The other four describes stayed 0-fail, so the mutation is
localised to the document gate exactly as intended. Reverted; see final green.

## Session-2 resumption audit (2026-07-27)

The previous session died mid-calibration, so the FIRST action was proving no
deliberate-red mutation was still applied:

- Read every enforcement call site: `browsing_context.spl` (all 8 delegations),
  `net/cookie_store.spl` (`validate_set_cookie` / `cookie_applies` /
  `script_visible` all present), `net/cors.spl` (no `==` origin compare left,
  `cors_url_origin` gone), `script/{clipboard,navigator,storage,network}_api.spl`,
  `net/fetch.spl`, and `security/origin_policy.spl` itself.
- Ran the whole enforcement spec cold: **46 total, 46 passed, 0 failed**
  (`build/brwire_2/green_jit_1.log`). A surviving mutation could not have
  produced that.
- Out-of-tree backup at `/tmp/brwire2_backup/` before touching anything.

## Final verification

| run | log | verdict |
|---|---|---|
| baseline green, JIT | `build/brwire_2/green_jit_1.log` | 7/8/6/7/9/9 — **46 total, 0 failed** |
| Red 4 applied, JIT | `build/brwire_2/red4_can_access.log` | **46 total, 5 failed** |
| final green, JIT | `build/brwire_2/green_jit_final.log` | 7/8/6/7/9/9 — **46 total, 0 failed** |
| final green, interpreter | `build/brwire_2/green_interp_final.log` | 7/8/6/7/9/9 — **46 total, 0 failed** |

Per-describe, both engines identical:
`cross-document access is refused at the call site` 7/0 ·
`response reads are gated by CORS` 8/0 ·
`cookie attachment is gated by the cookie policy` 6/0 ·
`storage is partitioned per origin` 7/0 ·
`permission-gated calls are default-deny` 9/0 ·
`an opaque origin gets nothing` 9/0.

**No deliberate-red mutation remains in the tree.** Verified twice: by reading
every enforcement call site, and by the two final all-green runs above (Red 4's
signature was 5 failures, so a residual mutation could not hide behind them).

## Follow-ups (not this lane)

- `security/origin_policy.origin_from_url_text` re-derives scheme/host/port by
  hand. Lane URLPARSE has since made `Url.parse` return `Option<Url>` and fixed
  the userinfo host spoof (`http://good.com@evil.com/`), so BRORIGIN's
  derivation should delegate to it. `security/**` is read-only for this lane.
- `resource_loader.spl` carries no origin at all; enforcement for loads
  currently lives at `BrowsingContext.read_response`. Giving the loader a
  requester origin is a separate increment.
- Renderer/network/GPU process split and WPT/Test262 remain blocked; this lane
  delivers in-process policy enforcement, NOT sandboxing.
