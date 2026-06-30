<!-- codex-research -->
# Simple TUI Dependency Size Local Research

Date: 2026-05-27

## Question

Can the Simple TUI app become C-termios-small by refactoring dependencies, or
does it require a bottom-up rewrite?

## Evidence

The startup audit in `doc/09_report/startup_size_performance_audit_2026-05-27.md`
shows:

| Lane | Bytes | Loaded libs | Result |
|---|---:|---|---|
| C termios TUI | 14472 | libc, ld-linux | ok |
| Simple standalone TUI core-c-bootstrap | 26864 | libm, libc, ld-linux | ok |
| Simple full TUI app simple-core | 92328 | libm, libc, ld-linux | ok |

The standalone Simple TUI lane uses the narrow `app.ui.tui.screen` ANSI path and
is close enough to the C lane to prove the TUI primitive itself does not require
a rewrite. The large row is the full app closure.

Current Simple core rows also retain `libm.so.6`; the C counters do not. This is
tracked in `doc/08_tracking/bug/simple_core_loaded_libm_gap_2026-05-27.md`.

## Findings

- The size gap is primarily dependency closure and platform-library selection,
  not terminal rendering logic.
- Keeping TUI off GUI/web/shared-app parsing paths is the right first move.
- The compiler/linker path should avoid unused platform libraries, especially
  `libm`, for core lanes.
- Network, TLS, compression, mmap preload, GUI, and web support should be
  explicit capsules/features rather than default TUI dependencies.
- A full rewrite would throw away a working narrow lane without addressing the
  remaining core runtime floor.

## Recommendation

Do not rewrite the TUI app bottom-up yet. Continue dependency refactoring and
closure control. Revisit a rewrite only if the full app still pulls unwanted
modules after feature capsules, symbol-driven platform library selection, and a
thin app entrypoint are in place.
