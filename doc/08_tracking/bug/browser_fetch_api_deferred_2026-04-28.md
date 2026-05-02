# Browser fetch API host bindings deferred

- **Date:** 2026-04-28
- **Reporter:** Stream B5 (lint recovery — real stubs)
- **Status:** Open / Deferred
- **Lint rules:** STUB003, L:stub_impl

## Summary

`install_browser_fetch_api(runtime: JsRuntime)` in `src/lib/common/web/browser_session.spl:1192` is a real stub: the body was a bare `pass_dn` with no rationale. It now uses `pass_dn("...")` form so the lint recovery is unblocked, but the function still does no work.

## Why it is stubbed

To implement `install_browser_fetch_api` analogously to `install_storage_api` (which calls `runtime._define_method_on(storage_id, "getItem", NATIVE_STORAGE_GET_ITEM)` etc.), three pieces are needed but absent at this layer:

1. `NATIVE_FETCH_*` (or equivalent) host-method constants — none are defined in the file or its imports.
2. A target object id to attach `fetch` / `Request` / `Response` / `Headers` onto. `install_storage_api` takes a `storage_id`; the fetch installer takes only `runtime`, so the contract for what gets defined is undecided.
3. URL parsing, header marshalling, and request/response body lifecycle handlers in the underlying native layer; these are part of the WHATWG fetch spec and require runtime work outside `browser_session.spl`.

## Proposed milestone

Schedule alongside the next browser-engine networking pass that adds `NATIVE_REQUEST_*` / `NATIVE_RESPONSE_*` host method constants. Once those land, this function should:

1. Define a `fetch` global on the window/global object.
2. Define `Request`, `Response`, `Headers`, `URL` constructors as host classes.
3. Wire them through to `host_get/post/...` runtime calls already used elsewhere in the browser session.

## Workaround applied

`pass_dn("...")` with rationale string and a comment block pointing here. No behavior change — the function was already a no-op; this just satisfies REQC001 (pass_dn requires a comment) and STUB003 lint recovery.
