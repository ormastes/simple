# Simple Browser Standard Case Inventory

Date: 2026-06-06

Purpose: seed the browser hardening work with stable case IDs for standards
coverage. Status is intentionally conservative: a row is `covered` only when
there is an executable SPipe or a traceable external-suite mapping.

Sources checked:

- WHATWG HTML Standard, Web Developers edition, Elements index, last updated 2026-06-05: https://html.spec.whatwg.org/dev/indices.html
- ECMA-262 2025 language specification: https://tc39.es/ecma262/2025/
- WebAssembly Core Specification 3.0, release 2026-06-04: https://webassembly.github.io/spec/core/
- RFC 9110 HTTP Semantics: https://httpwg.org/specs/rfc9110.html

## HTML Element Cases

Each listed tag gets at least one parser/rendering smoke case. Interactive tags
also need an event/action case when BrowserSession UI access is wired.

| Category | Tags | Base cases |
|---|---|---|
| Document metadata | `html`, `head`, `title`, `base`, `link`, `meta`, `style` | `HTML-TAG-<tag>-001` parser/tree case; `HTML-TAG-title-002` title extraction; `HTML-TAG-link-002` stylesheet request case |
| Sections | `body`, `article`, `section`, `nav`, `aside`, `h1`, `h2`, `h3`, `h4`, `h5`, `h6`, `hgroup`, `header`, `footer`, `address`, `main`, `search` | `HTML-TAG-<tag>-001` block fallback/render case |
| Grouping | `p`, `hr`, `pre`, `blockquote`, `ol`, `ul`, `menu`, `li`, `dl`, `dt`, `dd`, `figure`, `figcaption`, `div` | `HTML-TAG-<tag>-001` tree/render case; list tags add child containment case |
| Text-level | `a`, `em`, `strong`, `small`, `s`, `cite`, `q`, `dfn`, `abbr`, `ruby`, `rt`, `rp`, `data`, `time`, `code`, `var`, `samp`, `kbd`, `sub`, `sup`, `i`, `b`, `u`, `mark`, `bdi`, `bdo`, `span`, `br`, `wbr` | `HTML-TAG-<tag>-001` inline text preservation; `HTML-TAG-a-002` link activation/navigation case |
| Edits | `ins`, `del` | `HTML-TAG-<tag>-001` inline/block fallback case |
| Embedded | `picture`, `source`, `img`, `iframe`, `embed`, `object`, `video`, `audio`, `track`, `map`, `area` | `HTML-TAG-<tag>-001` parser/attribute case; media elements add unsupported-safe fallback case |
| Tabular | `table`, `caption`, `colgroup`, `col`, `tbody`, `thead`, `tfoot`, `tr`, `td`, `th` | `HTML-TAG-<tag>-001` table tree case; `HTML-TAG-table-002` cell text layout fallback |
| Forms | `form`, `label`, `input`, `button`, `select`, `datalist`, `optgroup`, `option`, `textarea`, `output`, `progress`, `meter`, `fieldset`, `legend` | `HTML-TAG-<tag>-001` parser/render case; controls add UI access action/value case |
| Interactive | `details`, `summary`, `dialog` | `HTML-TAG-<tag>-001` parser/render case; `HTML-TAG-<tag>-002` state toggle case |
| Scripting | `script`, `noscript`, `template`, `slot`, `canvas` | `HTML-TAG-script-001` inline execution; `HTML-TAG-script-002` external/module request; `HTML-TAG-template-001` inert content case |

## JavaScript Case Families

| ECMA-262 area | Base cases |
|---|---|
| Lexical grammar and literals | `JS-LEX-001`, `JS-LITERAL-001` |
| Expressions and operators | `JS-EXPR-001`, `JS-OP-001` |
| Statements and declarations | `JS-STMT-001`, `JS-DECL-001` |
| Functions, classes, modules | `JS-FN-001`, `JS-CLASS-001`, `JS-MODULE-001` |
| Objects and built-ins | `JS-OBJECT-001`, `JS-ARRAY-001`, `JS-STRING-001`, `JS-PROMISE-001`, `JS-JSON-001` |
| Exceptions and async jobs | `JS-ERROR-001`, `JS-ASYNC-001` |
| Browser host bridge | `JS-BROWSER-FETCH-001`, `JS-BROWSER-WASM-001`, `JS-BROWSER-WEBGPU-001` |

## WebAssembly Case Families

| Wasm area | Base cases |
|---|---|
| Module/header/sections | `WASM-MODULE-001`, `WASM-SECTION-001` |
| Control instructions | `WASM-CONTROL-001` |
| Parametric, variable, table, memory, numeric instructions | `WASM-PARAM-001`, `WASM-VAR-001`, `WASM-TABLE-001`, `WASM-MEMORY-001`, `WASM-NUMERIC-001` |
| Imports/exports and JS API | `WASM-IMPORT-001`, `WASM-EXPORT-001`, `WASM-JSAPI-001` |
| Trap/fail-closed behavior | `WASM-TRAP-001` |

## HTTP/HTTPS Case Families

| RFC 9110 area | Base cases |
|---|---|
| Methods | `HTTP-METHOD-GET-001`, `HTTP-METHOD-HEAD-001`, `HTTP-METHOD-POST-001`, `HTTP-METHOD-PUT-001`, `HTTP-METHOD-DELETE-001`, `HTTP-METHOD-CONNECT-001`, `HTTP-METHOD-OPTIONS-001`, `HTTP-METHOD-TRACE-001`, `HTTP-METHOD-PATCH-001` |
| Status classes and invalid status handling | `HTTP-STATUS-1XX-001`, `HTTP-STATUS-2XX-001`, `HTTP-STATUS-3XX-001`, `HTTP-STATUS-4XX-001`, `HTTP-STATUS-5XX-001`, `HTTP-STATUS-INVALID-001` |
| Message fields and content semantics | `HTTP-HEADER-001`, `HTTP-CONTENT-001`, `HTTP-COOKIE-001` |
| HTTPS secure-context bridge | `HTTPS-SECURE-CONTEXT-001`, `HTTPS-FETCH-WASM-001` |

## Current Executable Evidence

- Browser JS/WASM bridge: `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`
- BrowserSession primitive controls: `test/01_unit/lib/common/web/browser_session_controls_spec.spl`
- BrowserSession primitive controls through textual UI access:
  `test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl`
  covers queryable and actionable UI nodes for back, forward, stop, home,
  favorite, address, and title controls through the common `UiAccessSnapshot`
  model.
- BrowserSession fetch/WASM chain: `test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
- BrowserSession HTTP status semantics: `test/01_unit/lib/common/web/browser_session_http_status_spec.spl`
  covers `HTTP-STATUS-2XX-001`, `HTTP-STATUS-4XX-001`, and
  `HTTP-STATUS-INVALID-001` for unknown valid status-code class fallback and
  invalid status processing as server-error class responses.
- BrowserSession HTML metadata tag slice:
  `test/01_unit/lib/common/web/browser_session_html_metadata_tags_spec.spl`
  covers `HTML-TAG-html-001`, `HTML-TAG-head-001`, `HTML-TAG-title-001`,
  `HTML-TAG-base-001`, `HTML-TAG-link-001`, `HTML-TAG-meta-001`, and
  `HTML-TAG-style-001`. The cases verify document metadata and standalone
  `title`/`style` content stay out of visible text extraction.
- BrowserSession HTML section heading tag slice:
  `test/01_unit/lib/common/web/browser_session_html_section_tags_spec.spl`
  covers `HTML-TAG-body-001`, `HTML-TAG-h1-001`, `HTML-TAG-h2-001`,
  `HTML-TAG-h3-001`, `HTML-TAG-h4-001`, `HTML-TAG-h5-001`,
  `HTML-TAG-h6-001`, `HTML-TAG-hgroup-001`, and `HTML-TAG-address-001`.
  The cases verify adjacent headings, grouped headings, and address text stay
  readable with line boundaries instead of collapsed tokens.
- BrowserSession HTML tag standard slice:
  `test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl` covers
  `HTML-TAG-main-001`, `HTML-TAG-section-001`, `HTML-TAG-article-001`,
  `HTML-TAG-nav-001`, `HTML-TAG-header-001`, `HTML-TAG-footer-001`,
  `HTML-TAG-aside-001`, `HTML-TAG-search-001`, and
  `HTML-TAG-template-001`. The `template` case verifies inert content remains
  in source HTML but is absent from visible body rendering.
- BrowserSession HTML scripting tag slice:
  `test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl`
  covers `HTML-TAG-script-001`, `HTML-TAG-noscript-001`, and
  `HTML-TAG-noscript-002`. The cases verify script-driven body updates,
  `noscript` hidden from visible rendering when scripting is enabled, and
  `noscript` visible when BrowserSession runtime is disabled.
- BrowserSession HTML text-level tag slice:
  `test/01_unit/lib/common/web/browser_session_html_text_level_tags_spec.spl`
  covers `HTML-TAG-em-001`, `HTML-TAG-strong-001`, `HTML-TAG-small-001`,
  `HTML-TAG-s-001`, `HTML-TAG-cite-001`, `HTML-TAG-q-001`,
  `HTML-TAG-dfn-001`, `HTML-TAG-abbr-001`, `HTML-TAG-data-001`,
  `HTML-TAG-time-001`, `HTML-TAG-code-001`, `HTML-TAG-var-001`,
  `HTML-TAG-samp-001`, `HTML-TAG-kbd-001`, `HTML-TAG-sub-001`,
  `HTML-TAG-sup-001`, `HTML-TAG-i-001`, `HTML-TAG-b-001`,
  `HTML-TAG-u-001`, `HTML-TAG-mark-001`, `HTML-TAG-bdi-001`,
  `HTML-TAG-bdo-001`, `HTML-TAG-span-001`, `HTML-TAG-br-001`, and
  `HTML-TAG-wbr-001`. The `br` case verifies a visible line break in text
  extraction; `wbr` remains an optional zero-width break.
- BrowserSession HTML ruby tag slice:
  `test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl`
  covers `HTML-TAG-ruby-001`, `HTML-TAG-rt-001`, and `HTML-TAG-rp-001`.
  The cases verify `rt` annotations are readable as parenthesized annotation
  text and `rp` fallback markers do not duplicate when ruby handling is active.
- BrowserSession HTML edit tag slice:
  `test/01_unit/lib/common/web/browser_session_html_edit_tags_spec.spl`
  covers `HTML-TAG-ins-001` and `HTML-TAG-del-001`. The cases verify plain
  text extraction preserves revision semantics with `[+inserted]` and
  `[-deleted]` markers, including nested inline markup inside each edit tag.
- BrowserSession HTML embedded tag slice:
  `test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl`
  covers `HTML-TAG-picture-001`, `HTML-TAG-source-001`, `HTML-TAG-img-001`,
  `HTML-TAG-map-001`, `HTML-TAG-area-001`, `HTML-TAG-iframe-001`,
  `HTML-TAG-object-001`, `HTML-TAG-video-001`, `HTML-TAG-track-001`,
  `HTML-TAG-audio-001`, and `HTML-TAG-embed-001`. The `img` and `area`
  cases verify `alt` text extraction; embedded container cases verify fallback
  text remains visible.
- BrowserSession HTML form tag slice:
  `test/01_unit/lib/common/web/browser_session_html_form_tags_spec.spl` covers
  `HTML-TAG-form-001`, `HTML-TAG-label-001`, `HTML-TAG-input-001`,
  `HTML-TAG-button-001`, `HTML-TAG-select-001`, `HTML-TAG-datalist-001`,
  `HTML-TAG-optgroup-001`, `HTML-TAG-option-001`, `HTML-TAG-textarea-001`,
  `HTML-TAG-output-001`, `HTML-TAG-progress-001`, `HTML-TAG-meter-001`,
  `HTML-TAG-fieldset-001`, and `HTML-TAG-legend-001`. The value-bearing
  control cases verify `input value` text plus `progress`/`meter` value
  summaries.
- BrowserSession HTML interactive tag slice:
  `test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl`
  covers `HTML-TAG-details-001`, `HTML-TAG-details-002`,
  `HTML-TAG-summary-001`, `HTML-TAG-dialog-001`, and
  `HTML-TAG-dialog-002`. The cases verify closed `details` exposes only
  summary text, open `details` exposes detail text, closed `dialog` is hidden,
  and open `dialog` fallback text is visible.
- BrowserSession HTML table tag slice:
  `test/01_unit/lib/common/web/browser_session_html_table_tags_spec.spl`
  covers `HTML-TAG-table-001`, `HTML-TAG-caption-001`,
  `HTML-TAG-colgroup-001`, `HTML-TAG-col-001`, `HTML-TAG-thead-001`,
  `HTML-TAG-tbody-001`, `HTML-TAG-tfoot-001`, `HTML-TAG-tr-001`,
  `HTML-TAG-th-001`, and `HTML-TAG-td-001`. The case verifies row boundaries
  as newlines and cell boundaries as tabs in text extraction.
- BrowserSession HTML grouping tag slice:
  `test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl`
  covers `HTML-TAG-p-001`, `HTML-TAG-hr-001`, `HTML-TAG-pre-001`,
  `HTML-TAG-blockquote-001`, `HTML-TAG-ol-001`, `HTML-TAG-ul-001`,
  `HTML-TAG-menu-001`, `HTML-TAG-li-001`, `HTML-TAG-dl-001`,
  `HTML-TAG-dt-001`, `HTML-TAG-dd-001`, `HTML-TAG-figure-001`,
  `HTML-TAG-figcaption-001`, and `HTML-TAG-div-001`. The list cases verify
  newline-separated `li` items and `dt: dd` definition text.
- HTML/CSS compatibility subset: `test/03_system/gui/wm_compare/html_compat_spec.spl` and `test/03_system/feature/web_platform/css/*_spec.spl`

## Current Real Red Evidence

- BrowserSession storage API collision case:
  `test/01_unit/lib/common/web/browser_session_storage_spec.spl` verifies that
  `sessionStorage` keys named `getItem` and `length` remain data keys without
  replacing the callable Storage API method surface. The previous placeholder
  failure branches have been replaced with explicit failure messages; the
  focused interpreter run is currently red before implementation.
- BrowserSession anchor UI access case:
  `test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl`
  verifies that page anchors appear as textual UI `link` nodes with resolved
  `href` metadata and can be clicked to navigate through registered session
  resources. The focused interpreter run is currently red before implementation.
- Simple browser page adapter case:
  `test/01_unit/lib/common/web/simple_browser_page_spec.spl` verifies rendered
  anchor, field, submit, GET submission, POST submission, and hit-test target
  behavior with explicit missing-target failure messages. The focused
  interpreter run is currently red before implementation.
- BrowserSession lifecycle slice:
  `test/01_unit/lib/common/web/browser_session_spec.spl` now has real failure
  messages for `about:blank` success, stopped pending-navigation rejection, and
  explicit network-navigation rejection. The converted lifecycle range has no
  placeholder assertions; the broader legacy spec still has additional
  placeholders queued for later conversion.
- BrowserSession page-loading slice:
  `test/01_unit/lib/common/web/browser_session_spec.spl` now has real failure
  messages for title/body extraction, inline scripts, zero-delay timers,
  external scripts, inline/linked/imported stylesheets, and an external module
  graph with named imports. The converted page-loading range has no placeholder
  assertions; the broader legacy spec still has additional placeholders queued
  for later conversion.
- BrowserSession module/export slice:
  `test/01_unit/lib/common/web/browser_session_spec.spl` now has real failure
  messages for inline module default/namespace imports, default class exports,
  named/default re-exports, export-star behavior, namespace re-exports, and
  multi-declarator variable exports. The converted module/export range has no
  placeholder assertions; the broader legacy spec still has additional
  placeholders queued for later conversion.
- BrowserSession module/script follow-up slice:
  `test/01_unit/lib/common/web/browser_session_spec.spl` now has real failure
  messages for repeated namespace/default re-export cases, async/defer classic
  script ordering, and deterministic document loading with the JS runtime
  disabled. The converted follow-up range has no placeholder assertions; the
  broader legacy spec still has additional placeholders queued for later
  conversion.
- BrowserSession globals/location slice:
  `test/01_unit/lib/common/web/browser_session_spec.spl` now has real failure
  messages for browser-like globals, navigator fields, document URL/ready state,
  full location URL parts, `location.href` mutation, `location.assign`, and
  `location.replace` history behavior. The converted globals/location range has
  no placeholder assertions; the broader legacy spec still has additional
  placeholders queued for later conversion.
- BrowserSession history/WebGPU/eval/storage slice:
  `test/01_unit/lib/common/web/browser_session_spec.spl` now has real failure
  messages for `history.pushState`, `history.replaceState`, secure/insecure
  WebGPU globals, eval-script document mutation sync, and storage/cookie
  persistence across page loads. The converted history/WebGPU/eval/storage
  range has no placeholder assertions; the broader legacy spec still has
  additional placeholders queued for later conversion.
- BrowserSession cookie/fetch/storage/history tail slice:
  `test/01_unit/lib/common/web/browser_session_spec.spl` now has real failure
  messages for cookie attribute/removal behavior, promise/fetch response
  settlement, blob metadata/text, transport rejection, script-owned location
  navigation, Storage method compatibility, and back/forward/reload. The full
  `browser_session_spec.spl` file now has no placeholder assertions.
- BrowserSession async promise/fetch response slice:
  `test/01_unit/lib/common/web/browser_session_async_spec.spl` now has real
  failure messages for promise adoption/rejection, Promise globals, pending fetch
  settlement, HTTP error response metadata/status text, response text/json/body
  consumption, and fetch request header serialization. The converted first async
  range has no placeholder assertions; the broader async spec still has
  additional placeholders queued for later conversion.
- BrowserSession async chained-fetch/finally slice:
  `test/01_unit/lib/common/web/browser_session_async_spec.spl` now has real
  failure messages for chained fetch cookie propagation, Set-Cookie filtering,
  out-of-order response settlement, and fulfilled/rejected `Promise.finally`
  chains. The full `browser_session_async_spec.spl` file now has no placeholder
  assertions.
- BrowserSession JS/WASM/HTTP streaming MIME red case:
  `test/01_unit/lib/common/web/browser_session_async_spec.spl` now includes a
  real red `WebAssembly.compileStreaming(fetch(...))` case requiring rejection
  when the response `Content-Type` is not `application/wasm`. The case uses a
  valid WASM payload with `text/plain` to prove header validation rather than
  byte validation alone.
- BrowserSession JS/WASM/HTTP instantiateStreaming MIME red case:
  `test/01_unit/lib/common/web/browser_session_async_spec.spl` now includes a
  real red `WebAssembly.instantiateStreaming(fetch(...))` case requiring
  rejection when the response `Content-Type` is not `application/wasm`, using
  the same valid WASM payload with `text/plain` to cover the instantiation
  streaming path separately from compile streaming.
- BrowserSession HTTP redirect red case:
  `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` now
  includes a real red `HTTP-STATUS-3XX-001` browser-fetch case requiring a
  same-origin `302 Location: /new` response to queue the redirected request and
  resolve the JavaScript `fetch(...).then(r => r.text())` chain only after the
  final `200` response.
- BrowserSession HTTP HEAD red case:
  `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` now
  includes a real red `HTTP-METHOD-HEAD-001` browser-fetch case requiring the
  pending request to preserve `method: HEAD` while exposing an empty
  `Response.text()` body to JavaScript even if the committed response includes
  body bytes.
- BrowserSession HTTP 303 POST redirect red case:
  `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` now
  includes a real red browser-fetch case requiring a `POST` request that
  receives `303 Location: /submitted` to queue the redirected request as `GET`
  with an empty body and resolve page JavaScript from the final response.
- BrowserSession HTTP 307 POST redirect red case:
  `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` now
  includes a real red browser-fetch case requiring a `POST` request that
  receives `307 Location: /upload-target` to queue the redirected request as
  `POST` with the original body intact before resolving page JavaScript from
  the final response.
- BrowserSession HTTP 308 POST redirect red case:
  `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` now
  includes a real red browser-fetch case requiring a `POST` request that
  receives `308 Location: /permanent-upload-target` to queue the redirected
  request as `POST` with the original body intact before resolving page
  JavaScript from the final response.
- BrowserSession HTTPS mixed-content red case:
  `test/01_unit/lib/common/web/browser_session_http_status_spec.spl` now
  includes a real red `HTTPS-SECURE-CONTEXT-001` browser-fetch case requiring
  an HTTPS page to block active `fetch("http://...")` mixed content before any
  network request is queued and expose the rejection to page JavaScript.
- BrowserSession JS/WASM/HTTPS mixed-content red case:
  `test/01_unit/lib/common/web/browser_session_async_spec.spl` now includes a
  real red `HTTPS-FETCH-WASM-001` case requiring
  `WebAssembly.compileStreaming(fetch("http://.../module.wasm"))` from an HTTPS
  page to reject as mixed content before any network request is queued.

## Next Red-Test Slices

1. Generate `HTML-TAG-<tag>-001` failing parser/render specs for every HTML
   tag above that lacks an executable mapping.
2. Generate `JS-*`, `WASM-*`, and `HTTP-*` failing specs for each family above
   before adding new implementation behavior.
3. Promote passing rows from this inventory into
   `doc/09_report/web_platform_feature_matrix.md`.
