# Simple Web Browser Engine Production Hardening — Feature Requirements

Selection: Feature Option B — Secure interactive web core

## Requirements

- REQ-WEB-BROWSER-001: Production entrypoints shall use the accepted canonical
  browser engine and BrowserSession; research, fake-success, subprocess script,
  or parallel DOM/render/font paths shall not be production fallbacks.
- REQ-WEB-BROWSER-002: Production HTML shall use one canonical
  WHATWG-oriented tokenizer/tree-builder with deterministic recovery, document
  lifecycle, encoding, core semantic/form/image/link/scroll behavior, and safe
  unsupported-content fallback.
- REQ-WEB-BROWSER-003: The selected CSS profile shall implement cascade,
  inheritance, specificity, normal/inline/positioned layout, box model, flex,
  grid, typography, colors, backgrounds, overflow, transforms, transitions,
  and animations through structural and reference-render fixtures.
- REQ-WEB-BROWSER-004: Web layout/paint shall emit `DrawIrComposition`;
  Engine2D shall own execution, text, persistent device/session state, and
  transient font/cache resources.
- REQ-WEB-BROWSER-005: Page scripting shall use a browser-only JavaScript and
  Simple Script capability profile with a pinned syntax/built-in manifest;
  unsupported syntax/APIs shall report explicit errors.
- REQ-WEB-BROWSER-006: Timers, intervals, transitions/animations, selected Web
  Animations, and rAF shall share one monotonic clock, support cancellation,
  and produce observable multi-frame DOM/style/pixel changes.
- REQ-WEB-BROWSER-007: DOM mutation/event dispatch shall preserve live node
  identity and implement capture, target, bubble, cancellation, and supported
  default actions across script, events, layout, and paint.
- REQ-WEB-BROWSER-008: Pointer, click, keyboard, focus, blur, beforeinput,
  input, change, submit, scrolling, text editing, keyboard traversal, and
  accessible role/name/state shall work for supported controls.
- REQ-WEB-BROWSER-009: Back, forward, stop, reload, home, bookmark
  add/open/remove, links, and address navigation shall pass history,
  cancellation, persistence, focus, invalid-URL, and network-backed scenarios.
- REQ-WEB-BROWSER-010: HTTP/HTTPS loading shall use canonical URL/origin
  parsing, relative resolution, redirects, Fetch/CORS, credentials, abort,
  MIME handling, and bounded responses.
- REQ-WEB-BROWSER-011: HTTPS shall use maintained TLS and the platform trust
  store, validate chain/time/usage/service identity, enforce HSTS, and fail
  closed for invalid, expired, mismatched, untrusted, or failed connections.
- REQ-WEB-BROWSER-012: The browser shall enforce same-origin DOM/storage,
  CORS across redirects, CSP before execution, secure contexts, mixed content,
  and browser-owned navigation commits.
- REQ-WEB-BROWSER-013: Cookies/storage shall be origin-partitioned and enforce
  host-only/domain/path, Secure, HttpOnly, SameSite, and expiry.
- REQ-WEB-BROWSER-014: Hostile render/script work shall run in an OS-sandboxed
  renderer without direct filesystem/process/environment/device/listener or
  unrestricted network access; typed capabilities are brokered and validated.
- REQ-WEB-BROWSER-015: Support top-level http/https/audited internal pages.
  File/data/javascript/custom/external schemes require separately audited,
  user-gesture-bound exact capabilities or are denied.
- REQ-WEB-BROWSER-016: Pages shall not receive Node require/process/Buffer,
  generic native/FFI/IPC, or Simple runtime/process capabilities.
- REQ-WEB-BROWSER-017: Renderer CPU, wall time, memory, GC heap, recursion,
  DOM, response/decompression, redirects, connections, jobs, and frame work
  shall be bounded and observable.
- REQ-WEB-BROWSER-018: Navigation, cancel, renderer exit, and close shall
  release unreachable DOM, JS, listener, timer, image, layout, Draw IR, and
  Engine2D resources without stale callbacks, use-after-free, double-release,
  or retained cycles.
- REQ-WEB-BROWSER-019: A pinned WPT/Test262 subset, malformed-input corpus,
  security matrix, and fuzz/property corpus shall account for every claimed
  row and retain deterministic reproducers.
- REQ-WEB-BROWSER-020: Diagnostics shall expose safe navigation, renderer,
  script, TLS, sandbox, GC, frame, and limit failures without leaking secrets
  or host paths.
- REQ-WEB-BROWSER-021: Executable SSpec and mirrored manuals shall trace every
  requirement; missing platform/capability evidence remains blocked.

## Bookmark title implementation traceability

Status: **IMPLEMENTED STATIC / EXECUTION HELD**.

REQ-WEB-BROWSER-009 now traces bounded document-title transport and persistence
through `SBRF8`, the shared parent profile transaction
`hosted_browser_parent_toggle_bookmark`, and the exact four-step scenario in
`test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`.
The transaction owns mutation plus its ordered canonical snapshot read,
commits only after both succeed, and rolls back before parent revision/UI
publication on either error. A forged 513-byte decoded SBRF8 title is rejected
from its declared wire slice before title decode or admission.
Focused protocol, lifecycle, display, and file-backed restart coverage lives in
the matching unit/integration specs and generated `doc/06_spec` manuals.
These source and generated-manual artifacts are not an executable PASS; runtime
acceptance remains held until the scenario runs on an admitted current
pure-Simple full CLI with the admitted hosted artifact and SHA-256.

## Non-goals

- No claim of complete web-platform parity.
- No Engine3D browser shortcut.
- No absorption of the separate UI server/auth hardening lane.
