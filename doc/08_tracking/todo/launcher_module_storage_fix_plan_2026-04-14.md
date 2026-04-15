# SYS-GUI-006 Blocker 2 — `launcher:fail registered=0` Diagnostic

**Date:** 2026-04-14
**Author:** Round-15 OS-side triage agent (workspace `/tmp/simple-round15`)
**Ticket:** SYS-GUI-006 Blocker 2
**Upstream triage:** `doc/08_tracking/todo/sys_gui_006_round9_triage_2026-04-14.md`
**Related resume docs:**
- `doc/08_tracking/todo/sys_gui_006_bare_desktop_resume_2026-04-14.md`
- `doc/08_tracking/todo/sys_gui_006_with_apps_resume_2026-04-14.md`

## TL;DR

`DesktopShell.init()` calls `launcher_init()`, which
calls `launcher_register()` four times. In the **hosted interpreter** this
path works — `test/unit/os/services/launcher/launcher_spec.spl` asserts
`launcher_get_app_count()` is 5 after init+one register and passes. In the
**baremetal x86_64 desktop lane** (`examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`),
the same sequence leaves `launcher_get_app_count()` at `0` and the lane
emits:

```
[desktop-e2e] shell-ready
[desktop-e2e] launcher:fail registered=0
TEST FAILED
```

No OS-side code change in `src/os/**` can fix this without an escalation
to the compiler team, because **the underlying bug is in either
module-level array codegen or method-dispatch lowering for baremetal**,
both of which live in `src/compiler_rust/**` (off-limits for the OS-side
agent per the round-15 tracker gating).

## Evidence

### The shell.init body never prints

`src/os/desktop/shell.spl:248-265` (`DesktopShell.init`) prints these
markers unconditionally at the end of the body:

```
[shell] init: wm service initialized        (or ...init failed)
[launcher] Initializing app launcher...     (from launcher_init)
[launcher] Registered {app_count} default apps
[shell] init: launcher initialized
[shell] init: skipping taskbar ...
[shell] init: desktop shell initialized
```

The live serial trace verified by η on 2026-04-14 03:40 UTC (from
`sys_gui_006_bare_desktop_resume_2026-04-14.md`) contains NONE of these.
It goes directly from `[shell] new: WmService created` to
`[desktop-e2e] shell-ready`, then immediately `[desktop-e2e] launcher:fail
registered=0`. That is only possible if **the `shell.init()` call at
`desktop_e2e_entry.spl:102` never executed the `DesktopShell.init` body**.

### Module-level array globals in the launcher

`src/os/services/launcher/launcher.spl:58-71` defines:

```
var app_name: [text; 32]
var app_path: [text; 32]
...
var app_count: u64 = 0
```

`launcher_init()` clears these slots then calls `launcher_register()` four
times, which append via `app_count = app_count + 1`. If the baremetal
target does not materialize module-level fixed-size arrays with retained
storage across function boundaries (i.e. each load reads zeros or each
store silently writes to a stack-scoped shadow), `app_count` stays at 0
even after calls succeed.

## Two candidate root causes

Both are in compiler territory:

### (A) Method-dispatch mis-selection — likely primary cause

`desktop_e2e_entry.spl:97` already carries Agent δ's 2026-04-13 workaround:

```spl
var shell: DesktopShell = DesktopShell.new(ce2d.inner)
shell.init()
```

The comment documents that without the explicit `: DesktopShell` type
annotation, cross-module type inference for `X.new()` falls through to
`HirType::Any`, and native-build codegen silently picks the
shortest-named `.init` symbol in the whole module (dispatching
`shell.init()` to `Ps2Keyboard.init()`). The fact that no
`[shell] init:` / `[launcher] Initializing...` markers appear in the live
trace strongly suggests the annotation workaround is **not sufficient** —
probably because the method-resolution table is still keyed on the
unannotated MIR node, or because the same bare-method picker kicks in for
another call site in the chain.

The `[CODEGEN-AMBIGUOUS-METHOD]` diagnostic referenced in Agent δ's
commit note should already have been raised; check whether it was
suppressed or warning-only.

### (B) Module-level fixed-size array storage in baremetal

The launcher uses `var app_name: [text; 32]` at module scope. If
Cranelift / native codegen lowers these as per-function stack arrays
instead of `.bss` globals, the cross-function mutation pattern
(`launcher_init` populates, `launcher_register` appends,
`launcher_get_app_count` reads) breaks: each function sees its own zeroed
copy.

This is the same class of bug flagged as "module-level array storage bug
(baremetal global arrays) — Agent alpha" in the round-9 triage as a
sibling of Blocker 1.

## Why no OS-side fix is possible

- Moving the registry into a returned struct from `launcher_init()` and
  passing it through every call site would require changing ~40 public
  API entry points across `src/os/desktop/dock.spl`, `shell.spl`,
  `src/os/services/mod.spl`, the WM, and every test. That is a weeks-long
  refactor and still does not address cause (A).
- Rewriting `launcher_init()` to avoid module-level arrays (e.g. spelling
  them inside a single `Launcher` singleton struct stored in a
  `Lazy<Launcher>` cell) hits the **same** storage question — baremetal
  would need global-cell codegen to work reliably.
- Adding more typed-variable annotations in `desktop_e2e_entry.spl` was
  already done in Agent δ's round-13 fix and did not restore
  `desktop-ready`.
- Guardrails in the round-15 tracker explicitly disallow touching
  `src/compiler_rust/**`.

## What the compiler team needs to do

Priority order:

1. **Verify (A)** with a minimal repro: two modules, each declaring
   `class X { fn init() }` and `class Y { fn init() }` with distinct
   bodies that print. A baremetal entry with
   `var y: Y = Y.new(); y.init()` should print Y's body — regression
   test this.
2. **Verify (B)** with a minimal repro: one module with
   `var counter: u64 = 0` and `var slots: [i64; 4]`, plus
   `fn bump()`/`fn read() -> u64`. Call `bump()` three times, `read()`
   must return 3 in a baremetal ELF — regression test this.
3. Whichever fails first is the root cause of Blocker 2. Fix it, re-run
   `bin/simple os test --scenario=x64-desktop-test`, and confirm
   `[desktop-e2e] desktop-ready` appears.

## Pre-existing guard that will catch regressions once compiler is fixed

- `test/unit/os/services/launcher/launcher_spec.spl` — already covers
  `launcher_init` + `launcher_register` + `launcher_get_app_count`;
  passes in hosted.
- `test/unit/os/services/launcher/launcher_init_spec.spl` **(added
  2026-04-14 by this round)** — tightly-scoped guard asserting
  `launcher_get_app_count() > 0` immediately after `launcher_init()` so any
  future OS-side regression of `launcher_init()` itself is caught before
  it reaches the QEMU lane.

Once the compiler fix lands, the OS-side code does not need to change —
the existing call chain is correct. Re-run the x64-desktop-test scenario
to collect the `[desktop-e2e] desktop-ready` baseline.

## Round-15 decision

- Classification: **Large fix — baremetal codegen change**. Per
  round-15 guardrails, OS-side agent must NOT attempt a compiler fix.
- This document is the diagnostic pass-through to the compiler team.
- Blocker 2 remains open; the ticket owner should re-route it to the
  compiler team (or Agent α per the round-9 sibling triage) before the
  next SYS-GUI-006 live-lane attempt.
