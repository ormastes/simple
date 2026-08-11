# CLI help/dispatch/table drift — 1 phantom, 24 dead table entries, 44 undocumented

**Date:** 2026-08-11
**Status:** OPEN — spec is legitimately RED
**Severity:** Medium (user-facing CLI correctness)

## Summary

`test/01_unit/app/cli_help_alignment_spec.spl` previously hardcoded every
number it "checked":

- line 174: `val visible_help_count = 33`
- line 180: `val total_dispatch = 56`
- line 182: `expect(visible_help_count).to_equal(total_dispatch - 5)` → `33 == 51`

That assertion is **permanently false by construction**. No source change could
make it pass, and no source change could make it fail differently — it read
neither the help text nor the dispatch chain. It was a FAIL-FIRST placeholder,
not a gate, and its permanent red was being reported as an "18-command
help/dispatch drift" defect that the spec never actually measured.

The spec now READS the three CLI sources and counts. Every number is derived at
run time.

## What supersedes the old defect note

The "18-command drift" figure has no basis in any measurement. The real,
measured drift as of 2026-08-11 is below.

## Sources parsed

| Role | File | Commands |
|------|------|----------|
| Dispatch (**the only list that executes**) | `src/app/cli/_CliMain/main_and_help.spl` `str_eq(first, "X")` chain | 103 |
| Help text | `src/app/cli/cli_helpers.spl` `print_cli_help()` | 58 |
| Dispatch table | `src/app/cli/dispatch/table.spl` `CommandEntry(name: "X"` | 84 |

The executing elif chain is the oracle; "phantom" and "dead entry" are defined
relative to it.

## Measured drift

**1 phantom** — advertised in help, no dispatch branch (user gets an error):

- `check-capsule`

**24 dead table entries** — in `dispatch/table.spl`, unreachable:

`native-build, var, vscode, electron, check-capsule, check-skip, debug, qemu,
context, llm-process-gen, spipe-process-harness, record, security, search,
clean, bench, repl, jupyter-kernel, qualify-ignore, game, model3d, sound,
spritesheet, process`

**44 undocumented** — dispatchable with no help text. Held by a ratchet that
must not grow.

## Failing assertions

`test/01_unit/app/cli_help_alignment_spec.spl` (mirrored at
`test/unit/app/cli_help_alignment_spec.spl`), 2 of 8 examples RED:

- "every command in help text has a dispatch branch" → `[check-capsule]`
- "every dispatch-table entry has a dispatch branch" → 24 entries

These are correct specs failing on real drift. **Do not delete or weaken them
to obtain green.**

## Fail-closed proof

1. **Phantom detector.** Injected `print "  simple zzgateprobe ..."` into
   `cli_helpers.spl`. Offender list moved from `[check-capsule]` to
   `[zzgateprobe, check-capsule]` — the injected token was named. Reverted;
   `git diff src/app/cli/` clean.
2. **Ratchet.** Injected an `elif str_eq(first, "zzratchetprobe")` branch into
   `main_and_help.spl`. Undocumented count moved 44 → 45 and the ratchet went
   RED (`expected 45 to be less than 45`). Reverted; `git diff src/app/cli/`
   clean, zero residue.

## Vacuity guards

Set-difference assertions pass for free against an empty set, so a renamed file
or changed formatting would silently green the whole spec. Four positive
controls prevent that:

- all three source files exist;
- each extractor returns a plausibly-sized set (floors 50 / 40 / 20);
- named anchors `compile`, `build`, `check` are found in all three lists;
- flags and placeholders (`--notui`, `-c`, `<file.spl>`) are not counted as
  commands.

A companion staleness check asserts the undocumented count is `> 0`, so if the
drift is genuinely fixed the baseline must be tightened rather than left as
permanent slack.

## Unblock conditions

- **Phantom:** remove `check-capsule` from `print_cli_help()`, or give it a
  real dispatch branch (it is currently a subcommand of `check`).
- **Dead entries:** delete the 24 unreachable `CommandEntry` rows, or wire them
  into the elif chain.
- **Ratchet:** lower `UNDOCUMENTED_BASELINE` as help text is added. It is a
  ratchet, not a target — it may only ever decrease.

## Root cause

The command list is hand-maintained in five places
(`main_and_help.spl`, `cli_helpers.spl`, `dispatch/table.spl`,
`surface_alignment.spl`, `bootstrap_check.spl`) with only the first executing.
The durable fix is a single generated source of truth; this spec is the
interim gate that makes the divergence visible.
