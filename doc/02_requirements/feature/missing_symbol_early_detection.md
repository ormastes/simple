# Feature Specification – Missing-Symbol Early Detection

**Requirements:** (proposed — no requirement doc yet)
**Plan:** (proposed — no plan doc yet)
**Design:** (proposed)
**Status:** Draft

## Feature Description

A developer who declares, calls, or emits a symbol that is defined nowhere finds
out at push time on every platform, instead of at a Windows link weeks later or
as a SIGSEGV at first use.

## Problem this addresses

Measured over one Windows bootstrap session (2026-08-31/09-01). Every case below
built "successfully" on Linux while being broken:

| defect | what should have caught it | what actually happened |
|---|---|---|
| `mem_snapshot_record_promotion` called at `driver_hir_pipeline_support.spl:148`, defined nowhere | any closure-level call check | discovered at a Windows link |
| `rt_set_args` declared `__attribute__((weak))` | link | PE/COFF weak FUNCTIONS never resolve cross-TU — not via archive, `-Wl,-u`, or `--whole-archive`. Silent on ELF |
| `read_file` renamed to `fmt_read_file`, importers left stale | import resolution | nothing flagged; HIR failure much later |
| `runtime_core_host_services.c` dropped from the `tools.rs` source list by a merge | registration integrity | 18 symbols silently stopped compiling; the file was still there, so nothing looked missing |
| `runtime_terminal.c` never in the pure-Simple source list | link | 7 `rt_terminal_*` undefined; the link TOLERATED them, producing NULL GOT slots that SEGV at first use |
| `rt_print` registered for codegen, absent from the interpreter table | interpreter dispatch | Linux resolved it via a dynamic-SFFI fallback; Windows had no DLL and died |
| codegen emitted `rt_unwrap_or_trap`, runtime never defined it | link | the link printed "Unresolved symbol preview" and CONTINUED |

Two systemic causes make these invisible:

1. **The link tolerates undefined symbols** (`/FORCE:MULTIPLE,UNRESOLVED`,
   `--unresolved-symbols=ignore-all`, weak externals). A missing definition becomes a
   null pointer that crashes at first use — moving the failure out of the build and
   into runtime, the worst possible place.
2. **An unbacked `extern fn` is legal and silently returns nil**
   (`unregistered_extern_silent_nil_2026-08-01.md`). The population is known and frozen
   at ~1,466 by `check-unbacked-extern-ratchet.shs`: the project ratchets rather than
   fixes, so "declared but undefined" is a normal state.

The guard that exists for exactly this class,
`check-no-unresolved-runtime-symbols.shs`, measured GREEN on Linux on 2026-08-23
while Windows had 68 unresolved — it can pass **vacuously** when there is no
artifact to inspect.

## Scenarios

### Scenario: Calling a function that exists nowhere

**Given** a `.spl` file calls `mem_snapshot_record_promotion`, which no module defines
**When** the developer pushes
**Then** the gate fails naming the call site and the undefined symbol, identically on Linux, macOS and Windows

### Scenario: A registration list silently loses an entry

**Given** a merge removes `runtime_core_host_services.c` from the core-C source list while the file remains in `src/runtime/`
**When** the developer pushes
**Then** the gate fails, reporting a `.c` present in the tree but absent from every source list

### Scenario: Codegen emits a call the runtime never implements

**Given** codegen emits `rt_unwrap_or_trap` and no runtime TU defines it
**When** the native link runs
**Then** the link FAILS naming the symbol, instead of tolerating it and producing a NULL GOT slot

### Scenario: A weak definition that cannot resolve on the target

**Given** `rt_set_args` is `__attribute__((weak))` and the target is PE/COFF, where weak functions never resolve cross-TU
**When** the developer builds on any platform
**Then** the gate reports it as effectively undefined for that target, rather than failing only on Windows

### Scenario: Pre-existing debt does not block unrelated work

**Given** the tree already contains ~1,466 unbacked externs
**When** a developer pushes a change that adds none
**Then** the gate passes, failing only on NEW undefined symbols

## Acceptance Criteria

- [ ] A call to a name defined nowhere in the compiled closure fails a push-tier gate, naming file:line and symbol
- [ ] Every `.c` under `src/runtime/` (excluding vendored paths) appears in exactly one source list; zero or two lists fails
- [ ] Codegen-emitted runtime entry names are checked as a set against the runtime archive; any name with no definition fails
- [ ] A symbol whose only definition is weak, on a target where weak functions do not resolve cross-TU, is reported undefined for that target
- [ ] All gates run on Linux, macOS and Windows and are **fail-closed**: a run that inspected zero artifacts reports ERROR, never PASS
- [ ] Gates are ratcheted against the ~1,466-symbol baseline so pre-existing debt does not block unrelated pushes
- [ ] Each gate is wired in `config/check/must_check_gates.sdn` with a measured runtime cost recorded

## Out of Scope

- Eliminating the existing ~1,466 unbacked externs. Stage 2 of
  `unregistered_extern_silent_nil_2026-08-01.md` verified all 262
  `DEAD_DECLARATION` symbols were live (70 have real `.spl` call sites, 41 have
  non-`.spl` references, 111 are documented public API), so bulk deletion is unsafe.
- Removing link tolerance wholesale. Some is load-bearing: bootstrap
  chicken-and-egg, genuinely optional weak hooks, platform-gated code. The proposal
  is to make tolerance **explicit and allowlisted**, not to remove it.
- MIR lowering gaps (e.g. MCP's 120 errors). Those are feature-completeness, not
  detection — they already fail loudly.

## Notes

Mechanism analysis, including which tolerances are load-bearing versus accidental,
is at `doc/01_research/compiler/why_missing_symbols_do_not_fail_the_build_2026-09-01.md`.

Highest-value single item: the **static extern/definition cross-check** — the only
one that catches the defect before any link, on every platform, and it would have
caught most of the table above.
