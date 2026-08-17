# Generated GUI Full Web CSS Evidence Timeout

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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


---

## 2026-08-17 re-verification (wave_01 lane H3) — workaround confirmed still in place; gap unmeasured

Verified by reading current source, not by re-running the gate.
`examples/06_io/ui/generated_gui_web_parity_expected.spl:70` still calls the
narrowed local fixture:

```
val css = production_widget_css()
```

with `production_widget_css()` defined inline at lines 73-88 as a compact
hand-written subset (~15 rules). There is no import of
`app.ui.web.html.generate_css` anywhere in the file. So the state this report
describes is exactly the state of the tree: the compact-CSS workaround holds the
parity gate green, and the full ~38 KB production-CSS path remains unexercised.

**Verdict: OPEN and accurate as written, but it is not a silently-wrong-result
bug.** It is a coverage-plus-watchdog gap: the gate does not return a wrong
answer, it declines to measure the full-CSS lane at all. It was pulled into the
silently-wrong-results wave by its file path; it should be triaged with
performance/coverage work instead.

**Not attempted here:** re-running
`scripts/check/check-electron-generated-gui-web-parity-evidence.shs` against
full `generate_css("light")`. That needs an Electron run under a 60s watchdog on
a host where a bootstrap was holding ~98% CPU — the timing measurement would
have been meaningless, and a spurious timeout would have been indistinguishable
from the defect. The exact figure this report needs (CSS size, parse/layout
time, max RSS under full CSS) is therefore still unmeasured.
