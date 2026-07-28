# Simple Web Browser Engine Production Hardening — System Test Plan

## Claim boundary

This plan proves the selected bounded interactive profile. Existing unit and
derived-WPT suites are supporting evidence; they do not independently prove
the production browser, sandbox, HTTPS, live events, or GC/performance targets.

## Executable specifications

1. `test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`
   - production HTML/CSS/Draw IR;
   - script/animation clock;
   - page events/forms;
   - browser chrome/navigation.
2. `test/03_system/security/simple_web_browser_engine_security_spec.spl`
   - HTTPS/HSTS;
   - origin/CORS/CSP/mixed content;
   - cookies/storage;
   - schemes, Node/native denial, sandbox, IPC/limits/crash.
3. `test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`
   - startup/render/frame/input;
   - RSS, GC, lifecycle, soak, cancellation;
   - hot-path and regression budgets.

Mirrored manuals use the same paths below `doc/06_spec/`.

## Manual-visible steps

- Launch the production Simple browser
- Open the conformance page
- Render HTML and CSS through canonical Draw IR
- Run JavaScript and advance the browser clock
- Operate page controls
- Operate browser navigation controls
- Navigate through verified HTTPS
- Reject hostile origin and scheme requests
- Reject renderer host capability access
- Close the page and reclaim browser resources
- Measure production browser budgets

## Feature traceability

Each row has a normal (`N`), edge (`E`), and denial/error (`D`) case.

| Requirement | Executable spec | Cases | Required evidence |
|---|---|---|---|
| REQ-WEB-BROWSER-001 canonical path | production | PATH-N/E/D | binary identity, import/route receipt, no fallback |
| REQ-WEB-BROWSER-002 HTML | production | HTML-N/E/D | DOM snapshot, visible text, malformed recovery |
| REQ-WEB-BROWSER-003 CSS | production | CSS-N/E/D | computed style, layout, reference pixels |
| REQ-WEB-BROWSER-004 Draw IR | production | DRAW-N/E/D | serialized composition, Engine2D receipt, pixels |
| REQ-WEB-BROWSER-005 script profile | production/security | JS-N/E/D | DOM mutation, explicit unsupported error, no fake success |
| REQ-WEB-BROWSER-006 one clock | production | CLOCK-N/E/D | timer/rAF/CSS frames, cancel, deterministic timestamps |
| REQ-WEB-BROWSER-007 DOM/events | production | EVENT-N/E/D | stable IDs, exact phase trace, stale target |
| REQ-WEB-BROWSER-008 controls/a11y | production | CONTROL-N/E/D | UI access focus/value/role/actions and pixels |
| REQ-WEB-BROWSER-009 chrome/nav | production | NAV-N/E/D | address/history/stop/reload/home/bookmark receipts |
| REQ-WEB-BROWSER-010 URL/Fetch | security | FETCH-N/E/D | URL/origin/redirect/abort/MIME protocol trace |
| REQ-WEB-BROWSER-011 HTTPS/HSTS | security | TLS-N/E/D | trusted success, invalid cert matrix, no fallback |
| REQ-WEB-BROWSER-012 origin/CSP | security | ORIGIN-N/E/D | same-origin success, CORS/CSP/mixed denials |
| REQ-WEB-BROWSER-013 cookies/storage | security | STATE-N/E/D | two-origin partition, attribute rules, expiry |
| REQ-WEB-BROWSER-014 sandbox/broker | security | SANDBOX-N/E/D | syscall denial, typed broker success, startup failure |
| REQ-WEB-BROWSER-015 schemes | security | SCHEME-N/E/D | http/https/about success, exact file grant, denial matrix |
| REQ-WEB-BROWSER-016 no Node/native | security | CAP-N/E/D | globals absent, FFI/process/socket/file denied |
| REQ-WEB-BROWSER-017 limits | security/perf | LIMIT-N/E/D | below-limit success, exact limit, over-limit kill |
| REQ-WEB-BROWSER-018 lifecycle | perf | LIFE-N/E/D | cancel/close/restart counts and retained-resource plateau |
| REQ-WEB-BROWSER-019 corpora/fuzz | security | CORPUS-N/E/D | pinned manifest, unsupported list, retained reproducer |
| REQ-WEB-BROWSER-020 diagnostics | all | DIAG-N/E/D | typed safe diagnostics and secret/path redaction |
| REQ-WEB-BROWSER-021 SSpec/manual | all | MANUAL-N/E/D | executable paths, mirrored docs, no stubs/placeholder passes |

## NFR traceability

| Requirement | Executable spec | Cases |
|---|---|---|
| NFR-WEB-BROWSER-001 startup | budget | START-WARM/COLD/FAIL |
| NFR-WEB-BROWSER-002 first render/navigation | budget | RENDER-LOCAL/NAV/ERROR |
| NFR-WEB-BROWSER-003 frame pacing | budget | FRAME-CHANGED/UNCHANGED/STALL |
| NFR-WEB-BROWSER-004 input latency | budget | INPUT-POINTER/KEYBOARD/SCROLL |
| NFR-WEB-BROWSER-005 RSS | budget | RSS-WARM/60M/LIMIT |
| NFR-WEB-BROWSER-006 soak retention | budget | SOAK-WARM/10K/PLATEAU |
| NFR-WEB-BROWSER-007 GC pause | budget | GC-P50/P95/P99 |
| NFR-WEB-BROWSER-008 lifecycle reclaim | budget | RECLAIM-NAV/CLOSE/CANCEL |
| NFR-WEB-BROWSER-009 cancellation | production/budget | CANCEL-TIME/LATE/IDEMPOTENT |
| NFR-WEB-BROWSER-010 crash containment | security | CRASH-RENDERER/OTHER-SITE/PROFILE |
| NFR-WEB-BROWSER-011 security matrix | security | SECURITY-LINUX/MACOS/WINDOWS |
| NFR-WEB-BROWSER-012 conformance | security/production | WPT-CLAIM/PASS/UNSUPPORTED |
| NFR-WEB-BROWSER-013 fuzz | security | FUZZ-BUDGET/REPRO/NO-BYPASS |
| NFR-WEB-BROWSER-014 stability | budget | STABILITY-10K/STATE/RSS |
| NFR-WEB-BROWSER-015 regression | budget | REGRESS-BASELINE/DELTA/BLOCK |
| NFR-WEB-BROWSER-016 hot path | budget | HOT-NO-SPAWN/NO-RECREATE/READBACK |
| NFR-WEB-BROWSER-017 verify cap | all | VERIFY-ONCE/CYCLE-CAP/REPORT |

## Supporting evidence to retain

- tokenizer/tree-builder hardening specs;
- CSS cascade/variables and pinned derived-WPT specs;
- BrowserSession script/history/control specs;
- Draw IR and Engine2D specs;
- generic platform TLS and sandbox unit tests.

Supporting evidence is linked from the three production specs but does not
replace their live assertions.

## False-green repairs

Before reuse, `test/03_system/gui/browser_interaction_spec.spl` must fail when
`evidence.env` is missing and must replace noncanonical matchers. Validator-
fixture JSON, wrapper provenance, QEMU boot/font smokes, and screenshots without
structured interaction are not production browser evidence.

## Evidence paths

- Renderer-process scenarios require `HOSTED_WM_ARTIFACT` and its admitted
  `HOSTED_WM_ARTIFACT_SHA256` from
  `scripts/check/check-linux-hosted-wm-live-window-evidence.shs`. The spec
  hashes the exact native `src/os/hosted/hosted_entry.spl` artifact before
  launch; it does not accept `bin/simple` or silently substitute a worker.
- text/HTML/protocol/exec/log/artifact:
  `build/test-artifacts/<spec-relative-path>/`
- GUI images:
  `doc/06_spec/image/<spec-relative-path>/`
- generated manuals:
  `doc/06_spec/<spec-relative-path>.md`

## Platform matrix

| Platform | Required claim | Current design status |
|---|---|---|
| Linux x86_64 hosted native | full live PASS | required first |
| macOS arm64 hosted native | full live PASS before macOS claim | host required |
| Windows x86_64 hosted native | full live PASS before Windows claim | host required |
| SimpleOS x86_64/aarch64 QEMU | smoke/emulated only | cannot prove hosted sandbox/TLS |
| headless CPU/validator | supporting only | cannot prove production UI/sandbox |

Every row records target, runtime/binary hash, mode, renderer/backend,
native/emulated, status/reason, exact command, artifact hash, and timestamp.
Unavailable rows remain blocked or unsupported and do not count as PASS.

## Gate order

1. focused source checks and unit/integration specs;
2. production user-flow spec;
3. security/TLS/sandbox spec;
4. native budget/GC/soak spec;
5. pinned conformance/fuzz dependencies;
6. applicable compiler/lib/UI/whole-release and environment-facade gates.

Each final unchanged green command is recorded once.
