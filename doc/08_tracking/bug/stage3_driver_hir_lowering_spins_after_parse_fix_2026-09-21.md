# Stage 3 makes no observable progress in driver HIR lowering once the parse phase passes

- **Status:** OPEN
- **Found:** 2026-09-21, aarch64-unknown-linux-gnu, `origin/main` 63fdcd9ea57
  plus the `bind` rename (`work/elf-bind-reserved-word-20260921`)
- **Blocks:** Stage 3 self-host, and therefore Stage 4 and any redeploy

## Symptom

With the Stage 3 parse errors fixed (three locals named `bind`, a reserved word
the Rust seed does not reserve), Stage 3 parses all 1196 files with zero
`parser_error` and advances into HIR. It then stops making progress while
lowering the first module:

```
[build] phase=hir state=running unit_kind=modules done=1 total=841 remaining=840
        succeeded=1 cached=0 failed=0 task_done=2 task_total=6
        elapsed_ms=1081698 current=compiler.driver.driver
[BOOTSTRAP-PHASE] phase3:hir:imports:start src/compiler/80.driver/driver.spl
```

That is the last line written to `stage3-native-build.log`.

## What was measured (and what it does NOT establish)

Sampled every 2 minutes over 8 minutes, 62+ minutes after the last log write:

| time | RSS (KB) | CPU time | log size |
|---|---|---|---|
| 06:12:11 | 43600224 | 01:20:18 | 737606 |
| 06:14:11 | 43600224 | 01:22:18 | 737606 |
| 06:16:11 | 43600224 | 01:24:18 | 737606 |
| 06:18:11 | 43600224 | 01:26:18 | 737606 |

CPU time advances exactly 2:00 per 2:00 of wall clock — the process is `R` at
99.9% and genuinely burning a core. Across that window RSS is identical **to the
byte** and the log does not grow.

**This is NOT proof of a non-terminating spin, and an earlier draft of this
record overstated it.** When the process was killed at 06:37 (1h45m CPU) its RSS
had **dropped to 38,262,216 KB** — 5.3 GB below the flat value. A process stuck
in a tight loop does not release 5 GB. The drop is more consistent with a
collection or a phase boundary inside a stretch of work that happens to emit no
log lines.

What is established: **no forward progress was observable for 60+ minutes** — the
module counter stayed at `done=1`, the log did not grow, and a full core was
consumed throughout. What is NOT established: that the phase would never
terminate. It was killed, not observed to fail.

Discriminator for whoever picks this up: the FreeBSD QEMU lane on fixed `main`
reaches the same phase. If it also stalls there, the claim is two-host and much
stronger; if it completes, this was a very slow phase and the bug is a
performance/observability one, not a hang.

## Not caused by the parse fix

The change that got Stage 3 this far renames three mutable locals (`bind` ->
`sym_bind`) in `src/compiler/70.backend/linker/elf/{elf_static_link,
synthetic_sections,elf_boot_link}.spl`. It is 9 lines, locals only, and touches
nothing in `src/compiler/80.driver/`. The hang is in driver HIR lowering. It was
simply unreachable before, because the build died in the parse phase with
`[ERROR] phase 2 FAILED (2 recorded error(s))`.

## Reproduction

```sh
git checkout work/elf-bind-reserved-word-20260921    # or main + the 3-file rename
SIMPLE_CACHE_SCOPE=<lane> sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 \
  --produce-stage3-receipt=verify-landed-compiler-fix \
  --output=build/bootstrap-<lane>
SIMPLE_CACHE_SCOPE=<lane> sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --resume-stage3-from-admitted=<abs output> \
  --bootstrap-receipt=<abs output>/stage3-planner-admission.receipt
```

Stage 2 admits in ~13m38s at 16 jobs. Stage 3 reaches `phase3:hir:imports` in
about 18 minutes and does not leave it.

## Notes for whoever picks this up

- Stage 3 resume pins `--threads 1` unless `SIMPLE_NATIVE_BUILD_THREADS` is set,
  so this is single-threaded; it is not a deadlock between workers.
- Peak RSS before the spin was **43.6 GB**. The FreeBSD guest lane recorded
  28.4 GB as its peak and the QEMU wrapper still defaults to `QEMU_MEM=8G`; any
  in-guest repro needs far more than that.
- `signal=none` on the earlier parse failure and a live `R` state here both rule
  out the OOM killer.
- The phase emits no progress line between `phase3:hir:imports:start` and the
  next module, so "no log growth" cannot by itself distinguish slow from stuck.
  That observability gap is worth closing independently of the root cause.

## 2026-11-11 addendum (lane boot19) — BLOCKED (needs the sanctioned bootstrap; first status stays OPEN)

Verdict: BLOCKED. This row cannot be settled with the Rust seed
`bin/simple.exe`; it needs a self-hosted stage3 candidate to replay against.
The 2026-11-04 bootstrap triage in `doc/08_tracking/bug/bug_db.sdn:8422`
already adjudicated exactly this and prescribed the close-out procedure;
boot19 re-confirms the routing and adds no new diagnosis.

Exact grant command (from the 2026-11-04 adjudication, verbatim):

1. Fresh worktree rebased on origin/release/1.0.0 with no other bootstrap running.
2. `SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`
   (sanctioned bootstrap; yields `build/bootstrap/stage3/<triple>/simple` and
   `stage3-command.transcript`).
3. Replay the Symptom/Reproduction section of this doc with that stage3 binary
   under a timeout (stage3 cmd form: `build/bootstrap/stage3/<triple>/simple
   native-build <entry> ...`, or replay `stage3-command.transcript`) and
   capture rc plus last 50 log lines.
4. Append the observed rc and log here (and in `bug_db.sdn`) and set status
   closed if it no longer reproduces.

Context for the granted lane: several stage-2/3 blockers behind this
record's snapshot have since been fixed (entry-closure char/byte import drop —
`13d7746adc0e`; `local_symbol_index_slots` reset — merge `9e7e7a526edb`/PR
#7597; SSA duplicate-def slotting —
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:206-228`;
checked unwrap lowering — `e569d40037c7`), so there is a reasonable chance
the spin no longer reproduces. Per the adjudication, that is for the granted
bootstrap run to establish — not for seed-smoke or source inspection to
claim. The observability gap this doc notes (no progress line between
`phase3:hir:imports:start` and the next module) remains a legitimate
follow-up for the same lane.
