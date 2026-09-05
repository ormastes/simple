# NFR: `cs` — Caret Suite

Status: in development (2026-09-03)

## NFR-1 — Tools depend on sosix, not on native libraries directly

`cs`, the pane backend, and anything else in this lane call the **sosix host
facade** (`src/lib/nogc_async_mut/sosix/`). They do not call `tmux`, `/bin/sh`,
`ps`, or Win32 directly.

## NFR-2 — The sosix layer costs nothing on POSIX

Where sosix reaches the same POSIX primitive the caller would have used, the
forward must cost nothing. A real adapter is written only where the signature
genuinely must change, and every adapter is justified in the module header.

**Measured limitation (2026-09-03).** The intended mechanism — a renaming
re-export, `export use m.orig as sosix_orig` — **does not work**: it parses and
then binds nothing (`error[E1002]: function 'aliased' not found`). Confirmed
twice independently; repro and impact in
`doc/08_tracking/bug/no_renaming_re_export_blocks_zero_cost_facade_alias_2026-09-03.md`.
Because the facade's names are `sosix_`-prefixed while the primitives are
`process_*`/`which`, **no** symbol can currently be a true re-export.

The facade therefore uses `@always_inline` single-call pass-throughs (repo
precedent: `process_run_direct`, `process_kill_unchecked` in
`src/lib/nogc_sync_mut/io/process_ops.spl`). Callers still see only `sosix_*`,
and the forward should collapse at codegen.

State this plainly rather than claiming more than is true: the zero-cost
property currently rests on the **inliner**, not on the module system, and it is
not verified by any gate. Restore the structural guarantee when renaming
re-export lands.

## NFR-3 — Platform selection is compile-time for this tool

`cs` is built per host, so binding the platform at compile time is correct.

This is deliberately **narrower** than the seam-qualification bar in
`.claude/skills/spipe.md`, which REJECTS host-OS as a `variants/` axis using
`path_separator` as its example. That rejection is aimed at the **compiler**,
which is multi-target at runtime from a single binary — baking a host value
there regresses correctness. A per-host tool binary has no such property. Any
module in this lane that binds the platform at compile time must state this
distinction in its header, so the divergence from the bar is visible and
argued rather than silent.

## NFR-4 — The dashboard is testable without a terminal

`cs_render` and `cs_handle_command` are pure over `CsDashboard`; all I/O lives
in `cs_refresh` and the launch/kill paths. A spec can therefore assert layout
and command semantics with no tmux, no TTY, and no live agent.

## NFR-5 — Capability is established by positive probe

`pane_available()` proves tmux by resolving the binary *and* making a call that
succeeds. It is never inferred from `sosix_platform()` alone, and never from
grepping a binary for a symbol — both are documented false-green sources in
this repo.

## NFR-6 — Fail closed, never fake

A malformed pane line yields no pane rather than a pane with garbage fields. An
unreachable manager renders an honest status. A model that cannot run returns a
structured error. Absence of evidence is reported as absence, not as zero.

## NFR-7 — Reuse over reinvention

The suite reuses `chat_tui` widgets, `agent_runtime`, `multi_caret_manager`,
and the existing OpenAI-compatible client. It introduces no second TUI
framework, no second HTTP client, and no numbered module variants.
