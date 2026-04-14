# SYS-GUI-006 — Round 9 Triage & Cross-Ticket Impact

**Date:** 2026-04-14
**Author:** Agent theta (round-13 isolated workspace investigation)
**Purpose:** Consolidate Round-8 dual-blocker findings so downstream
tickets (SYS-GUI-007 disk lane, SYS-GUI-008 virtio-gpu baseline) can
make forward progress without waiting on a single monolithic resume.

This note supersedes nothing. It sits alongside:

- `doc/08_tracking/todo/sys_gui_006_bare_desktop_resume_2026-04-14.md`
  (Agent η / Round 8)
- `doc/08_tracking/todo/sys_gui_006_with_apps_resume_2026-04-14.md`
  (Agent zeta)

## TL;DR for SYS-GUI-008 owners

**SYS-GUI-006 is NOT LIVE-GREEN and cannot be unblocked from the
SYS-GUI-006 territory alone.** Two independent upstream regressions
must land first, both owned by other agents and both in directories
that the SYS-GUI-006 resume checklists explicitly forbid editing. A
Round-9 agent restricted to SYS-GUI-006 scope has no legal path to
close the gate. SYS-GUI-008 must either:

1. Wait for the two upstream fixes described below, OR
2. Stand up its virtio-gpu baseline against the same live lane that
   SYS-GUI-006 is waiting on — in which case it inherits both
   blockers 1:1 and will fail at the same `[desktop-e2e] launcher:fail`
   step, OR
3. Define its own entry scenario that bypasses
   `DesktopShell.init()` / `launcher_init()` and captures the
   virtio-gpu framebuffer from an intentionally bare kernel. This is
   a scope change for SYS-GUI-008 and needs an owner decision.

## Blocker state (re-verified against round-13 working copy)

### Blocker 1 — Interpreter semantic cascade on `Architecture.X86_64`

- **Territory:** `src/compiler_rust/**` (Agent γ / Z2).
- **Symptom:**
  `bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter`
  emits ~60 "Export statement references undefined symbol" warnings
  from `std.spec.*`, then hard-fails at
  `build_os(target)` with:

  ```
  semantic: method `X86_64` not found on type `Architecture`
  ```

- **Not** the `pub enum` after `@allow(...)` parser bug that γ already
  fixed in `src/compiler_rust/parser/src/parser_impl/items.rs`. That
  fix is present in the round-13 working copy but the cascade remains.
- **Sibling repro:** `test/system/engine2d_in_qemu_spec.spl`
  (`--mode interpreter`) fails identically. SYS-GUI-007 disk-lane
  prerun shows the same error on `Architecture.X86_64` and
  `Architecture.Riscv64`. Fixing this unblocks **three** gated
  tickets at once (SYS-GUI-006 bare, SYS-GUI-006 with-apps,
  SYS-GUI-007 disk, SYS-ENGINE2D).
- **Alternative shortcut:** make `--mode native` actually execute
  `it{}` bodies via the cranelift backend. The native path already
  parses the same type graph through `bin/simple os test
  --scenario=x64-desktop-test` without issue, which proves the bug
  is interpreter-local. This is the cheapest path forward for
  SYS-GUI-006 specifically.

### Blocker 2 — Live-lane regression: `launcher:fail registered=0`

- **Territory:** `src/os/**`, `examples/simple_os/**`
  (Agent α / δ). Note: `src/os/desktop/shell.spl` also appears as
  modified in the upstream working copy, which suggests a partial
  fix is already in flight — Round-9 needs to determine whether
  that WIP is the intended fix or an unrelated edit.
- **Live trace on 2026-04-14 (verified both by η and by theta in
  round-13 workspace):**

  ```
  [desktop-e2e] shell-ready
  [desktop-e2e] launcher:fail registered=0
  TEST FAILED
  ```

  Never reaches `[desktop-e2e] desktop-ready`, so even if Blocker 1
  clears, `wait_for_serial_marker(..., "[desktop-e2e] desktop-ready",
  60000)` will time out.

- **Probable regression site:** `DesktopShell.init()` calls
  `launcher_init()` internally
  (`examples/simple_os/arch/x86_64/desktop_e2e_entry.spl:105-108`),
  but `launcher_get_app_count()` returns 0. Either:
  1. `load_app_manifests()` in `src/os/desktop/shell.spl:718`
     returns empty at runtime (manifest dir missing / empty at
     boot image time), or
  2. Apps load into a module-level array that loses its contents
     across the load boundary — i.e. the **same** Agent-alpha
     module-level-array-storage bug that the with-apps resume
     checklist already blames. If (2), Blocker 2 is actually a
     downstream manifestation of Blocker 1's sibling "module-level
     array storage bug (baremetal global arrays) — Agent alpha" and
     fixing that in the compiler also clears the live lane.
- **Triage ask for Round-9 alpha/delta:** confirm whether the
  launcher gets any manifests at all (add a one-line
  `serial_println("[shell] manifests loaded={len(manifests)}")`
  trace before `launcher_init()` and re-run
  `x64-desktop-test`). If that prints `0`, it is the load_app_manifests
  side; if it prints `N` and `launcher_get_app_count()` still returns
  `0`, it is the launcher-side array storage bug and Agent alpha owns it.

## Why a SYS-GUI-006 agent cannot land either fix

Both resume checklists list explicit Do-NOT zones:

- Bare-desktop checklist: `src/compiler_rust/**` and implicitly the
  launcher/shell boot path (Agent α / δ territory).
- With-apps checklist: `src/os/**`, `examples/simple_os/**`,
  `src/compiler_rust/**`, compositor capture/tolerance, qemu runner,
  os harness — all off-limits.

That leaves a SYS-GUI-006 agent with exactly these legal edits:

- `test/system/simpleos_desktop_framebuffer_spec.spl` (bare)
- `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl` (with-apps)
- `test/baselines/simpleos_desktop_framebuffer/**` (bare baseline)
- `test/baselines/simpleos_desktop_with_apps_framebuffer/**`
  (with-apps baseline)
- Tracker docs under `doc/08_tracking/todo/`

None of those can fix the semantic cascade or the launcher regression
without violating the tracker rules (fake baseline, soften the gate,
or reach into forbidden territory). Any "forward progress" on
SYS-GUI-006 that isn't documentation would require softening a gate
that exists specifically to catch this class of regression — which the
tracker explicitly prohibits.

## Recommended action for the next round

1. Re-assign Blocker 1 to a compiler-authorised agent (Z2 / γ lineage)
   with scope explicitly broadened to the semantic analyzer and
   interpreter module loader — **not** just the parser. Minimum
   acceptable output: `bin/simple test
   test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter`
   reports zero "Export statement references undefined symbol"
   warnings for `std.spec.*` and `build_os(target)` resolves
   `Architecture.X86_64`. OR land the `--mode native` it-body path.
2. Re-assign Blocker 2 to Agent α or δ with the triage-print above.
   Minimum acceptable output: `bin/simple os test
   --scenario=x64-desktop-test` emits `[desktop-e2e] desktop-ready`
   on the serial log.
3. Only then schedule a Round-10 SYS-GUI-006 agent to run the
   verification sequence in the Round-8 bare-desktop checklist and
   commit the real PPM baseline.
4. SYS-GUI-008 owners should treat SYS-GUI-006 as **blocked-external**
   in their own tracker and not plan any work that depends on
   SYS-GUI-006 being LIVE-GREEN until both items above land. If
   SYS-GUI-008 cannot wait, take the option-3 scope change (bare
   virtio-gpu kernel entry) and write it into the SYS-GUI-008 plan.

## What this round did NOT change

- No spec files edited.
- No baseline files committed (placeholder PPM stays zero-byte by
  design — the gate must keep hard-failing until a real capture
  lands).
- No compiler or OS source touched — both are off-limits for a
  SYS-GUI-006-scoped agent.
- SYS-GUI-006 status remains **NOT LIVE-GREEN / blocked on two
  upstream regressions**. Do not mark it green on the basis of this
  document.
