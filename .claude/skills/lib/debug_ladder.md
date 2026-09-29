# Debug Ladder

Canonical 5-step training ladder for this repo, distilled from
`doc/01_research/infra/spipe/spipe_bug_management_debug_knowledge_evidence.md`
§8, §8.1, §15.1, §6.4. This extends `.claude/skills/lib/debug.md` (the D0-D12
evidence workflow) — read that first for the full case lifecycle; this file
is the mandatory ordered sequence plus the hard rules and the host-verified
commands to run each step on THIS machine, today.

Verified on 2026-09-05, host darwin/arm64. Every command below was actually
run. A command not run is marked `BLOCKED: <reason>` instead of guessed.

## Environment facts (verified, do not assume otherwise elsewhere)

- `command -v gdb` → **not found**. `command -v lldb` → `/usr/bin/lldb`
  (present). On macOS, `gdb` is generally unavailable/unsigned; `lldb` is the
  native debugger here.
- `bin/simple` is the **bootstrap-only** compiler (`Simple Bootstrap Compiler
  v1.0.0-beta`). It has no `run`/`test`/`lint`/`debug` subcommands — only
  `compile` and `native-build`.
- The only full-CLI-shaped invocation that actually runs on this host today is
  the fresh Rust seed:
  `/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple <file.spl> [args]`
  (verified: prints its bootstrap-seed warning, then runs the file, ~6s
  startup). It also answers `compile`, `native-build`, and prints `--help`
  listing `test`/`lint`/`fmt`, but those subcommands are **not actually wired
  in this build** — verified: `simple test <spec>` printed
  `WARNING: test daemon unavailable; running directly` then
  `error: unknown command 'test'`. Treat `test`/`lint`/`debug`/`bug-add` as
  BLOCKED on this seed; only `simple <file.spl>` (bare run) is confirmed
  reliable.
- Attempting the full self-hosted CLI by interpreting it through the seed
  (`simple src/app/cli/main.spl -- debug doctor <file>`) was tried and is
  **BLOCKED here**: it loads ~3500 lines of lint warnings, JIT-falls-back to
  the interpreter on `src/app/cli/main.spl` itself
  (`Cannot infer field type: struct 'ByteSpan' field 'data'`), and returns
  with no `debug doctor` output inside a 100s budget. Do not rely on this path
  for `simple debug doctor|replay|reproduce` on this host; `replay`/`reproduce`
  are documented upstream as incomplete regardless.
- `bin/bug` is a **broken symlink** (`../tools/bug-cli/bin/bug`, target does
  not exist). Leave it alone; do not "fix" it as part of debugging.
- T32 is lab-only and not wired here: `.mcp.json` has no `t32` server entry,
  and the scripts `doc/07_guide/app/tools/cli.md:277-279` names
  (`scripts/t32_start_stm.shs`, `scripts/t32_enable_gdb.shs`) do not exist in
  this tree. Do not imply T32 runs in this environment; see
  `.claude/skills/lib/t32.md` for what it covers in general.

## The 5 steps (must run in this order)

### 1. Check the log

Look at what the run already told you before doing anything else.

```bash
SIMPLE_LOG=debug /Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple <file.spl>
```

Verified: this seed accepts `SIMPLE_LOG=debug` and runs the file (same binary
verified above for bare `run`). For module-specific tracing use
`SIMPLE_LOG=interpreter=trace`. See `.claude/skills/lib/debug.md` "Logging &
IR Export" for the full env-var table (`--emit-ast`/`--emit-hir`/`--emit-mir`,
`SIMPLE_AOP_LOG_CALLS`, `--gc-log`) — those flags are on the same binary and
inherit this verification.

### 2. Review the code changed, with commits

```bash
jj log -r 'main@origin..@' --no-graph -T 'commit_id.short() ++ " " ++ description.first_line() ++ "\n"'
jj diff -r <suspect-rev> --stat
jj diff -r <suspect-rev>            # full diff of the suspect range
```

Verified: both `jj log` and `jj diff --stat` ran clean against this repo's
current working range. Use `--stat` first to scope, then the bare `diff` on
the narrowed range. Per `.claude/rules/vcs.md`, never resolve a rebase
conflict at the tip — this is read-only inspection, not a rebase, so no
conflict handling applies here.

### 3. Use the debugger on the bug-related tests

Three tiers. **Pick by symptom: a crash goes to A, a wrong value goes to C.**
Reaching for lldb on an interpreted logic bug is the common wasted hour.

**A. Native debugger (lldb) on the seed process itself** — for a native
crash/fault in the Rust seed or in a compiled artifact:

```bash
lldb -b -o "b main" -o "run <file.spl>" -o "bt" -o "continue" -o "quit" \
  -- /Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple
```

Verified: this exact invocation launched the seed under lldb, stopped at
`b main` (16 locations resolved), printed a real backtrace
(`frame #0: ... simple\`main`), then `continue` ran the file to completion and
exited 0. Swap `b main` for a symbol/line in the crashing native path once you
have one (e.g. from a Rust seed panic backtrace or `check-c-runtime` failure).
`gdb` is not available on this host — use `lldb`, not a gdb recipe.

**B. Interpreter-mode stepping (DAP / language-level breakpoints)** — for
stepping Simple *source* execution logic (variables, step, breakpoint at a
`.spl` line):

```
BLOCKED: the DAP server and `simple debug` subcommand live in the full
self-hosted CLI (src/app/cli_debug/main.spl, src/app/dap/), which is not
deployed on this host (bin/simple is bootstrap-only) and does not finish
inside a reasonable budget when interpreted through the Rust seed (see
environment facts above). The DAP MCP tool contract (debug_create_session,
debug_set_breakpoint, debug_stack_trace, debug_step, debug_continue,
debug_get_variables) is documented in .claude/skills/lib/debug.md and
doc/07_guide/app/lsp_dap/debug_profile_dap.md — use it once a full-CLI binary
is deployed; do not claim it works here until re-verified against one.
```

**C. Probe script — the tier you will actually use most.** For an *interpreted
logic* bug (a wrong value, not a crash), lldb on the seed binary tells you almost
nothing: you are debugging the interpreter, not your program. Do not burn time
there. Write a small `.spl` probe that calls the suspect function across a range
of inputs and prints real values, then read the output:

```bash
/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple run <probe.spl>
```

This is what actually located the defect in the first real exercise of this
ladder: sweeping `bytes_to_wire`/`wire_to_bytes` over 0-255 exposed a
round-trip corruption for byte values >= 128 that reading the source did not
reveal (the source looks correct, and is, for ASCII). Sweep the whole domain,
not the one value from the ticket.

**Import-path gotcha that will cost you time if you don't know it:** in a probe
script, `std.*` imports resolve wherever the file lives, but **`lib.*` imports
resolve relative to the probe file's own directory, not your cwd.** A probe
placed in `/tmp` or the scratchpad silently cannot reach `lib.` modules. Put the
probe next to the code under test, or import through `std.*`.

T32-script-style scripted runs also belong at this step when hardware/lab
targets are in play — see `.claude/skills/lib/t32.md` and `.claude/agents/t32.md`,
but note the T32 caveat above: no server is wired into this repo's `.mcp.json`.

### 4. Reproduce the bug as a test, plus a similar-bug-prevention test

This step **is** the existing repo rule in `.claude/rules/testing.md`: every
bug fix ships two specs — one reproducing the exact defect, one
generalization spec probing adjacent code paths — both cited in the
`doc/08_tracking/bug/` record. Do not invent a competing version of this rule;
follow the one already in force.

Running a single spec on this host — **this works, use it** (corrected
2026-09-05 after the first real exercise; an earlier revision of this file
wrongly marked it BLOCKED):

```bash
/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple run <spec.spl>
```

It executes the spec and prints a real per-example result plus a machine-readable
verdict line, and its exit code is meaningful (0 green, 1 red). Measured on two
specs written during that exercise:

```
4 examples, 0 failures
SPEC FILE VERDICT: ...repro_spec.spl outcome=OK    declared>=4 executed=4 passed=4 failed=0
4 examples, 3 failures
SPEC FILE VERDICT: ...generalization_spec.spl outcome=ERROR declared>=4 executed=4 passed=1 failed=3
```

**Always read `executed=`, not just `failed=0`.** `executed=0 failed=0` is a
vacuous run, not a pass — the spec never ran. This is the negative-evidence rule
applied to the test runner itself.

What genuinely does NOT work here: `simple test <spec>` — verified
`error: unknown command 'test'` on the seed, after a "test daemon unavailable;
running directly" fallback message. Use `run` instead; do not conclude specs are
unrunnable on this host.

Bug-DB entry points (`bin/simple bug-add --id=X --reproducible-by=<test>`,
`bin/simple bug-gen`) are documented in `src/app/bug_add/main.spl`,
`src/app/bug_gen/main.spl`, `src/app/bug_resolve/main.spl`, with the
missing-test-link validation enforced at
`src/lib/nogc_sync_mut/database/bug.spl:589`. Verified BLOCKED on this host:
`bin/simple` (bootstrap-only) does not recognize `bug-add`, and `bin/bug` is a
broken symlink (`tools/bug-cli/bin/bug` does not exist) — do not fix the
symlink as part of this task; file the doc record by hand
(`doc/08_tracking/bug/`) until a working binary exists.

### 5. DEFERRED — dumps, reproducing-situation asserts, C/Rust debugging

Named per the user's explicit instruction ("not now, later"). Do **not**
build this. When it is picked up, it corresponds to research doc §9 (tiered
capture: black-box / runtime-gated / diagnostic-build / lab-trace), §9.4-9.5
(assertion policy, persistent crash area), and the `debug-firmware` /
`debug-software` core-and-minidump-processing extensions in §15.2-15.3.

**When the dump writer lands (2026-09-05, still deferred — read before
picking this up):** the CONSUMER side of this step already exists and is
strict — `src/app/cli_debug/evidence_inspect_v1.spl` reads and validates a
`debug-evidence-bundle-v1` manifest field by field, and
`src/app/cli_debug/evidence_replay_v1.spl` does semantic replay. The
PRODUCER side (a dump writer / coredump-minidump capture / ELF-core parser)
does not exist anywhere in this repo. The exact contract a future writer
must satisfy is pinned at
`doc/07_guide/app/debug/debug_evidence_bundle_contract.md`, with a
conformance spec at
`test/01_unit/app/cli_debug/debug_evidence_bundle_contract_v1_spec.spl`. Do
NOT claim dump-based debugging works — a real inspection currently crashes
on an unrelated pre-existing reader defect, see
`doc/08_tracking/bug/debug_evidence_inspect_receipt_id_field_missing_2026-09-05.md`.
On arrival this step becomes: R0 diagnose-from-dump (build/session/capture
identity, then semantic replay) without rerunning the failing program.

## Hard rules (research doc §15.1)

- Never claim PASS from absent output.
- Never symbolize with mismatched binaries (build ID / symbols must match the
  exact artifact that crashed).
- Never repeat a refuted hypothesis without satisfying its recorded rerun
  condition.
- Never treat "bug disappeared" as a cause.
- Never edit generated wiki or raw SDN directly.
- Never execute downloaded/untrusted artifacts.
- Never enable broad instrumentation without a stated budget and a stated
  question.
- Always preserve exact commands, tool versions, seeds, and hashes — every
  command in this file was recorded verbatim for that reason; do the same
  when you extend it.

## Negative-evidence rule (research doc §6.4)

A zero-result probe is not evidence by itself. It only counts once you show:

- the exact check and exact environment/build it ran against;
- the expected signal, and that the observed absence is real (not truncation);
- proof the observation channel was actually live — a **positive control**
  that the same channel *can* emit a signal when the condition is true;
- the scope of the exclusion and the condition that would justify a rerun.

Example: "grep found 0 matches" is not evidence unless you also show the run
reached the instrumented path, the output wasn't empty/truncated for an
unrelated reason, the probe's build ID matches the symbols you're reading, and
a positive-control case proves the probe fires when it should.

## Symptom -> first check (distilled from research doc §8; repo-relevant classes only)

| Symptom | First discriminators | First check on this host |
|---|---|---|
| Crash / fault (native) | exact fault type, first failing thread, valid symbols, repeatable | `lldb -b -o "run ..." -o "bt"` on the seed binary (step 3A above); confirm build id matches the binary you're symbolizing |
| Hang / timeout | CPU idle vs busy, same PC vs changing, blocked-wait vs interrupt storm | attach lldb and sample PC a few times (`process interrupt` / `bt` / `continue` repeated), or reduce input via bisection before adding logging |
| Wrong result | first boundary where the invariant breaks; deterministic vs history-dependent | bisect with `SIMPLE_LOG=debug` + `--emit-hir`/`--emit-mir` to find the first stage where output diverges from expectation |
| Intermittent / flaky | probability, seed, environment strata, temporal clustering | rerun with fixed seed/order where possible; do not conclude from one pass — record numerator/denominator, not a single boolean |
| Boot / reset (bootstrap stage) | reset source, stage reached, build id | check `doc/08_tracking/bug/` for the matching stage (stage1-4) incident pattern before re-deriving one; see `.claude/rules/bootstrap.md` |
| Build failure (seed / native) | compiler exit code, first error, whether it's E0432/E0599-class | read the compiler's own diagnostic first (step 1) before touching code; `bin/simple compile`/`native-build` --help lists exact flags, verified above |

## Reproduction ladder R0-R5 (research doc §7.2, L572-585)

"Reproduced" is not a claim on its own — it must **name its level and its
oracle** (what result proves the bug, and what would disprove it). Use the
lowest level that is sufficient; a root cause found at R0 may still need an
R2/R3 test after the fix (diagnostic necessity vs. post-fix prevention are
different questions).

| Level | Name | Typical use | Reachable on THIS host? |
|---|---|---|---|
| R0 | Offline evidence replay | Parse an existing dump/log/trace; no rerun | Yes — step 1 (log review) and step 2 (`jj diff`) are R0 |
| R1 | Deterministic trace/event replay | Replay recorded events/simulator input | Yes — the probe-script tier (step 3C) replaying recorded inputs |
| R2 | Unit/component fixture | Minimal source/input reproducer | Yes — step 4 (`simple run <spec.spl>`), verified above |
| R3 | Integration/system simulation | Multiple modules/services | Partial — `simple run` on a multi-module spec works; the full-CLI daemon path is BLOCKED (see environment facts) |
| R4 | Full system/HIL/firmware | Timing, hardware, power, boot, real controller | BLOCKED here — no lab hardware, T32 not wired (see environment facts); SimpleOS/QEMU work belongs to `.claude/rules/board-runnable.md`, not this ladder |
| R5 | Field/production-equivalent recurrence | Rare production-only condition | BLOCKED here — no production telemetry channel on this host |

## Sealed prediction

A hypothesis is not usable until it states its **predicted observation before
the run** — write the prediction down first, then execute, then compare.
Corollary: **a check that cannot distinguish at least two live hypotheses is
not worth running** — if every hypothesis predicts the same outcome, the check
has zero discriminating power and only wastes the budget. This is already the
letter of `bug_hypotheses.predicted_observations` and
`bug_experiments.expected_discriminating_outcomes` in
`doc/01_research/infra/spipe/spipe_bug_management_debug_knowledge_evidence.md`
§6.2 — this section just makes it an explicit ladder step: predict, then run,
never the reverse order.

## Anti-flywheel rules (research doc §30, ~L1729-1752) — read this before tuning any checklist

A scoring loop that scores work, edits its own guidance from the score, then
re-scores with that same guidance **can raise its numbers without raising
capability** — the "wrong flywheel": `more history -> longer prompt -> same
cases score higher -> publish everything`. **This repo already runs a loop
shaped exactly like that**: the sspec training loop (checklist -> low-effort
worker -> `sh scripts/check/sspec-train.shs` score -> edit the checklist ->
re-score on the same specs) landed today
(`doc/00_llm_process/feature_expert/modern_sspec/skill.md` "Training loop"
section). Three cheap counter-rules, apply them to that loop and to any future
debug-knowledge scoring loop:

- **Held-out set** — keep specs/cases the checklist was NOT tuned on, and
  report their score separately from the tuned batch.
- **No same-case validation** — a knowledge edit derived from case X may not
  be validated by re-scoring case X; validate on a case the edit was not
  written to fix.
- **Leak gate** — guidance text must not contain answer-bearing identifiers
  (specific bug IDs, unique symbol names, rare literal strings copied from the
  answer) that let a worker pattern-match the fix instead of deriving it.

Concretely for this repo: `sh scripts/check/sspec-train.shs <dir>` is the
scoring tool in active use. A future improvement to the checklist should score
a held-out spec set the checklist was not tuned against, not just re-run the
same batch that motivated the edit.

## Agent pointers

`.claude/agents/debug.md` and `.claude/agents/debug-analyst.md` reference this
file for the mandatory step order and host-verified commands — see the
one-line pointer added to each.
