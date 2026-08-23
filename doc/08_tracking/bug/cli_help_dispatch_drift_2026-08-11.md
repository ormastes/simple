# CLI help/dispatch/table drift — 1 phantom, 24 dead table entries, 44 undocumented

**Date:** 2026-08-11
**Status:** **REOPENED 2026-08-23** — regressed past the 2026-08-11 resolution; see the REGRESSION section appended at the end. (Was: RESOLVED 2026-08-11 — see RESOLUTION section.)
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

---

## RESOLUTION 2026-08-11 — all three drift classes closed

### 1. Phantom `check-capsule` — WIRED, not removed

The implementation was already present and exported:
`src/app/cli/check_capsule.spl` defines `handle_check_capsule(args: [text])`,
re-exported from `src/app/cli/__init__.spl:30`. Only the dispatch branch was
missing, so help was telling the truth about a feature that had merely lost its
entry point. Removing the help lines would have deleted a working feature.
Added to the elif chain in `main_and_help.spl` (plus the `use` import).

### 2. The 24 "dead" table entries — dispositioned individually

Every entry's declared `app_path` was checked for existence and for `fn main`.

- **`native-build` — never dead.** It is dispatched *before* the elif chain, at
  `main_and_help.spl` `if str_eq(args[0], "native-build")`, deliberately
  bypassing `filter_internal_flags` so `--backend=` survives. The spec's
  extractor only knew the `str_eq(first, "X")` form and so reported a live
  command as both phantom and dead. The extractor now scans both forms — a
  strengthening of the oracle, and the reason this entry needed no source change.
- **`bench` — obsolete, REMOVED.** `src/app/bench/main.spl` does not exist and
  neither does `src/app/bench/`. The entry described a command that could never
  run under any wiring. Deleted from `dispatch/table.spl` with a comment.
- **The remaining 22 — WIRED.** `var, vscode, electron, check-capsule,
  check-skip, debug, qemu, context, llm-process-gen, spipe-process-harness,
  record, security, search, clean, repl, jupyter-kernel, qualify-ignore, game,
  model3d, sound, spritesheet, process`. All 22 implementations exist and expose
  `fn main`, i.e. they are finished apps that lost their CLI entry point, not
  aspirational entries. Each got an elif branch delegating via `cli_run_file`
  with `_cli_args_from(filtered_args, 1)` (the `grammar-doc` precedent), except
  `check-capsule` (direct `handle_check_capsule`) and `repl` (routed to the
  existing `cli_run_repl`, which already backs the no-argument default).

### 3. Undocumented ratchet — 44 → 0

Help text was added in `print_cli_help()` for all 44 previously undocumented
commands plus the 22 newly wired ones and `native-build` (66 lines, grouped into
five new sections). `UNDOCUMENTED_BASELINE` is now **0**, its floor.

The companion staleness guard, which asserted `undocumented > 0` to stop the
baseline becoming permanent slack, would have contradicted a genuine fix. It was
replaced by `expect(undocumented).to_equal([])` — exact equality that also names
offenders. That is strictly stronger than the bound it replaces, not a relaxation.

### Fail-closed re-proof (after the fix, gate GREEN 8/8)

1. Injected `print "  simple zzgateprobe ..."` into `print_cli_help()`.
   → exit **1**, `expected [zzgateprobe] to equal []`. Reverted.
2. Injected `elif str_eq(first, "zzratchetprobe"): return 0` into the chain.
   → exit **1**, both ratchet assertions RED
   (`expected 1 to be less than 1`, `expected [zzratchetprobe] to equal []`).
   Reverted.
3. Post-revert: `grep -c zzgateprobe\|zzratchetprobe` = 0 in both files; spec
   back to `passed=8 failed=0`.

### Root cause — NOT rewritten, deliberately

Five hand-written registries remain. A single source of truth is achievable in
principle: the natural shape is a fallback at the end of the elif chain that
looks up `find_command(first)` in `dispatch/table.spl` and runs `entry.app_path`,
which would make the table execute and permanently kill the dead-entry class.
It was **not** done, for a reason that is about verifiability, not taste:

- The gate's oracle is *by definition* the elif chain. A table fallback moves
  the oracle, so the spec's extractor would have to be rewritten at the same
  time as the thing it measures — the gate could not witness its own change.
- The chain is not uniform. Branches variously pass `filtered_args`,
  `_cli_args_from(filtered_args, 1)`, or `raw_args`; several do per-command
  munging (`check` handoff/delegate, `ios` flag prepending, `native-build`
  pre-chain bypass). A generic fallback cannot reproduce those without a
  per-command argument policy — i.e. a fifth registry.

The incremental fix was done instead and is fully verified. The unification
remains the durable fix and is recorded here rather than silently dropped.

### Recorded, NOT changed: `src/app/cli/dispatch.spl` is fully shadowed dead code

`src/app/cli/dispatch.spl` (150 lines) duplicates `dispatch/__init__.spl` and
never executes. It is **not** deleted: it is a published API surface with a
committed baseline entry at `doc/08_tracking/api_surface/baseline.sdn:20-24`, so
removing it needs a bootstrap and a baseline update. Recorded here as follow-up.

### Adjacent pre-existing RED (untouched, not caused by this change)

`test/01_unit/app/cli_command_inventory_spec.spl` is RED 9/23 with the *same*
anti-pattern this bug was originally about: hardcoded literals
(`expect(all_commands.len()).to_equal(51)` against a hand-written 62-element
list, and seven "fail-first" placeholder assertions). It reads no source file, so
it is unaffected by this fix and cannot be greened by one. It needs the same
rewrite `cli_help_alignment_spec.spl` received.

**Status: RESOLVED.** Gate `cli_help_alignment_spec.spl` 8/8 GREEN,
0 phantoms, 0 dead table entries, 0 undocumented commands.


---

## REGRESSION — re-measured 2026-08-23 (docs/help lane)

Reopened because the drift is now **worse than at the 2026-08-11 resolution**
(which recorded 1 phantom, 24 dead entries, 44 undocumented). Measured by
RUNNING the deployed binary, not by reading source:

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
60,650,360 bytes, 2026-08-23 04:47:05. It self-identifies as a bootstrap seed
(`WARNING: this Rust-built Simple binary is a bootstrap seed only`), so every
number below is the seed's `help.rs` surface — no full pure-Simple CLI is
deployed to compare against.

| finding | measured |
|---|---|
| `--help` goes to **stderr**, never stdout | `simple --help \| wc -l` = **0**; `simple --help 2>&1 >/dev/null \| wc -l` = **226**. `simple --help \| grep x` silently finds nothing. |
| listed vs registered | **39** commands in `--help` vs **85** `CommandEntry` rows in `src/app/cli/dispatch/table.spl` — **57 registered commands undocumented** (was 44) |
| phantom (advertised, unregistered) | **`update`** (`help.rs:137`) and **`cache`** (`help.rs:141-144`, "cache info/list/clean") — in no table (was 1 phantom) |
| self-referential stubs | `simple list` -> `Package management is handled by the Simple app.` / `Run: simple list`; same for `tree`, `install` (`driver/src/cli/commands/pkg_commands.rs:9`; registered `table.spl:518, 525, 462`) |
| `build` absent from `--help` | `simple build` (no args) exits **0** printing "Simple Build System" having built nothing; its subcommands `bootstrap/lint/fmt/check` are **Rust-workspace tooling**, not user-project compilation. Nothing in any help text says so. `table.spl:536` |
| unknown command misreported | `simple nosuchcmd` -> `error: file not found: nosuchcmd` (falls through to the script-path route); no "did you mean" |
| working but in no help and no table | `stats`, `doc-coverage` — dispatched via `src/app/cli/stats_entry.spl:12` and `src/app/cli/doc_coverage_command.spl:437`, declared implemented in `src/app/cli/surface_alignment.spl:96,:45`, exposed as MCP tools (`:258,:232`); CLI-discoverable only through MCP |
| Rust-only, will vanish on the pure-Simple binary | `examples-check` (`help.rs:20`), `diagram` (`help.rs:53-55`) — advertised and functional, unregistered in `table.spl` |

**Structural cause of the drift, and why nothing catches it:** `table.spl`
carries **no help or summary strings at all** — `CommandEntry` is
`(name, app_path, env_override, needs_rust_flags)`. The help text lives in
`src/compiler_rust/driver/src/cli/help.rs` (plus a separate pure-Simple
`src/compiler_rust/lib/std/src/tooling/help.spl`). The two surfaces have no
shared source of truth, so registering a command does nothing to its help and
removing one leaves its help behind.

**Nothing was changed by the lane that measured this** — it is a docs/help-text
lane and `help.rs` is seed product logic. The user-facing docs were corrected to
stop implying `--help` is complete: `.claude/rules/commands.md` gained a
"The CLI `--help` is incomplete and partly wrong" section pointing here.

**Not fixed, and deliberately not described as if it worked:** the 57
undocumented commands, the 2 phantoms, the 3 stubs, the stderr routing, and the
missing-file diagnostic all stand as of 2026-08-23.
