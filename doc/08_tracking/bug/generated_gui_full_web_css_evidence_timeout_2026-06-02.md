# Generated GUI Full Web CSS Evidence Timeout

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Status
open

## Context
`examples/06_io/ui/generated_gui_web_parity_expected.spl` briefly imported
`app.ui.web.html.generate_css("light")` so the Electron generated-GUI parity
evidence could render the same full production Web UI CSS page used by browser
backends.

## Failure
`sh scripts/check/check-electron-generated-gui-web-parity-evidence.shs` produced the
expected HTML and ARGB artifacts, then the Simple runner exceeded the 60-second
watchdog while running under `SIMPLE_LIB=src`.

Observed log excerpt:

```text
simple_status=pass
html_has_style=true
html_has_app_shell=true
pixel_count=6912
[memory-guard] SIMPLE_LIB=src contains 600+ .spl files
[watchdog] wall-clock timeout (60s) exceeded
error: example timed out after 60s: examples/06_io/ui/generated_gui_web_parity_expected.spl
```

The generated HTML artifact was about 38 KB, dominated by full WM/web CSS. The
evidence fixture now uses a compact production-widget CSS subset so the current
parity gate remains runnable, but full production CSS rendering remains a
separate performance and coverage gap.

## Expected
The Simple web renderer evidence path should render full generated Web UI CSS
fixtures without exceeding the watchdog, or provide an explicit budgeted
full-CSS evidence lane that reports CSS size, parse/layout time, and max RSS.

## Repro

```sh
SIMPLE_TIMEOUT_SECONDS=60 SIMPLE_LIB=src bin/simple run examples/06_io/ui/generated_gui_web_parity_expected.spl --mode=interpreter --clean
```

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
