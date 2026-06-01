<!-- codex-research -->
# Pure Simple Profile-Guided Executable Optimization NFR Options

Date: 2026-06-01

## Option 1: Conservative Safety Baseline

Targets:
- `.sprof` disabled means no profile file I/O in hot paths.
- Profile data never bypasses semantic guard facts.
- Executable layout changes preserve entry, relocation, and symbol metadata.

Pros: safest first slice.
Cons: weak performance budgets.
Effort: Small.

## Option 2: Measured Profile-Guided Optimization

Targets:
- Profile load startup overhead under 5% on representative fixtures.
- Native counter overhead under 3% when instrumentation is enabled.
- Pure-Simple layout optimizer must report before/after size, startup, and
  representative runtime.
- No hot request full-tree scans, shell-outs, or repeated profile rereads.

Pros: performance claims require evidence.
Cons: needs benchmark harnesses and reports.
Effort: Medium.

## Option 3: Bare-Metal Trap Budget Gate

Targets:
- Software-breakpoint counters auto-disarm when trap overhead exceeds budget.
- Hot loop breakpoints are replaced by sampled/timer counters.
- Breakpoint patch/restore must be idempotent across panic/restart paths.
- QEMU and hardware-unavailable evidence must be separated.

Pros: directly addresses bare-metal slow-running breakpoint risk.
Cons: requires target-specific debug and QEMU evidence.
Effort: Large.

## Recommended Selection

Use Options 2 and 3 together for the full plan.
