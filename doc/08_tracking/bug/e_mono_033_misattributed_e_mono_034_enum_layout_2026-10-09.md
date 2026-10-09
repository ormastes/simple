# E-MONO-033 "1 generic call site unspecialized" with call_sites=0: a misattributed E-MONO-034

Status: OPEN (composition-only code; not on release/1.0). Reduced producer repro found.
Date: 2026-10-09

## Symptom

9 targets of `build/rc1-small-large-next40` (005-office-cli, 028-os,
029-leak-check, 142-ui.electron, 161-play, 162-ide, 171-simple-lab,
176-ui.browser, 207-cli) fail with

```
[mono] generic_fns=13 call_sites=0 specializations=0 unresolved=1
error[E-MONO-033]: monomorphization left 1 generic call site(s) unspecialized
```

`call_sites=0` with `unresolved=1` looked unreachable because both counters
increment together in `rewrite_call`.

## Root cause

Every one of the 9 `diagnostics.json` files carries, immediately before the
E-MONO-033 line, `error: E-MONO-034: ambiguous declaring enum layout:
<owner>::<Enum>` (`compiler.semantics.safety_checker::SafetyError` for
028/029/207, `lib.common.ui.profile::Orientation` for 142/161/162/171/176,
`lib.common.ui.profile::SizeClass` for 005). The retained live-tail keeps only
`error[` markers, so the `error:`-prefixed E-MONO-034 line was dropped from the
logs. The guard lives only in the `phase3-generic-transport` composition
(commit `8061c3ffb6c` "fix(mono): retain canonical unit enum layouts across
specialization", squashed into `8940a0bcd56`; absent from `origin/release/1.0`):
its Step-1 loop over `module.enums` increments
`stats.unresolved_generic_calls`, pushes E-MONO-034 and `return modules`
BEFORE any call site is walked -- hence 0/1. The driver then counts every mono
diagnostic as an unspecialized call site, so the E-MONO-033 text is misleading.

Which of the four guard conditions fails is reproduced but not yet proven:

- Not a short-name collision on the enum itself: payload tracing on the
  reduced repro shows only `Spacing` (class in `ui.style` vs enum in
  `ui.design_tokens`) colliding, and it is requalified cleanly.
- A faithful two-module import cycle (`a` declares `enum Kind` + impl and
  imports `b`'s struct; `b` imports `Kind`) passes the guard
  (`unresolved=0`, producer run `e3`).
- A verbatim private copy of `src/lib/common/ui/profile.spl` +
  `viewport.spl` (each importing the other; profile also imports
  `common.ui.widget`) reproduces it with a 3-file entry
  (`unresolved=1`, producer run `e4`, 99 s). This is the smallest known repro.

## Where to look next

With `e4`, instrument the Step-1 loop (print `declaration.kind`,
`declaration.name`, `lookup_qualified_type_raw(owner, layout.name)` vs
`layout.symbol.id`, and whether `nominal_enum_layouts` already holds the key)
to pin the failing condition; the profile/viewport pair's distinguishing
feature versus the passing mini cycle is the transitive `widget` facade
(`export use`) and multiple enums with impls in one declaring module.

## Repro harness

`scratchpad/emono_repro/run.sh <name> <entry> [threads]` (REPO defaults to a
detached worktree of the producer's source revision `6bf3276a434`;
`COLD_INIT=1` for a fresh inventory, `PAYLOAD_TRACE=1` for HIR payload
tracing) runs the lane producer with the lane's exact flags on one entry.
