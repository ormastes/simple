# Stage 2 admission refuses because a concurrent session edits the source tree mid-run (2026-09-05)

Status: OPEN — not a compiler defect; the gate is behaving correctly

## Verdict

```
Stage 2: running bootstrap compiler sanity
Stage 2: proving struct receiver/runtime capability
error: refused incomplete Stage 2 admission provenance
stage: stage2
exit:  4
```

## What actually happened

Stage 2 is **fine**. Three separate runs on 2026-09-05 establish it:

- The native build succeeds: `Build complete: 821 compiled, 0 cached, 0 failed`,
  linking `build/bootstrap/stage2/aarch64-apple-darwin/simple` (136,216 KB) in
  1470.0s compile + 33.6s link.
- `stage2-sanity.env` records `status=pass` — `version_output=simple-bootstrap
  1.0.0-rc.1`, `unsupported_status=1` (the bootstrap CLI correctly refuses
  `run`), `frontend_smoke_status=0`.
- `stage2-receiver.env` records `status=pass`, `probe_exit=0`, with
  `candidate_sha256_before == candidate_sha256_after`.

The refusal comes from the four-part admission predicate at
`scripts/bootstrap/bootstrap-from-scratch.sh:2657-2662`, which requires the
tool-authority snapshot AND the source-inputs snapshot to be byte-identical
before and after the stage, plus both evidence files to say `status=pass`.

Measured on the failing run:

| input | result |
|---|---|
| `tool-authority-before.txt` vs `-after.txt` | identical |
| `stage2-sanity.env` | `status=pass` |
| `stage2-receiver.env` | `status=pass` |
| `source-inputs-before.txt` vs `-after.txt` | **DIFFERS — 14 entries** |

Decoding the differing `file-hex:` entries gives five files, all in one
directory:

```
src/app/llm_caret/gui.spl
src/app/llm_caret/main.spl
src/app/llm_caret/multi_caret_manager.spl
src/app/llm_caret/workbench/gui_page.spl
src/app/llm_caret/workbench/tui_view.spl
```

Their mtimes at 21:05 were 20:51, 21:02 and 21:00 — i.e. a **concurrent session
was editing them while the bootstrap ran**. The gate is doing exactly its job:
an artifact built from a tree that changed underneath it has no honest
provenance, so it is refused rather than admitted.

## Why this was hard to see

Two diagnostic paths reported the wrong thing and cost a full run each:

1. On a run that skipped the Rust rebuild, the failure printed
   `diagnosis: the log was NEVER CREATED, so nothing ever executed` — but
   `stage2-native-build.log` existed and ended in `Build complete`. The
   diagnosis was reading a *stale* log's state against a run that had not
   rebuilt.
2. The wrapper was launched by another session as
   `sh -c '… ; echo BOOTSTRAP_EXIT=$?'`, so the bootstrap's own stdout went to a
   terminal and nothing on disk captured it. `bootstrap-progress.log` recorded
   only `milestone=exit-1 main_log=absent`. **Re-running with stdout redirected
   to a file is what made the error text readable at all.**

Separately, and already filed as
`bootstrap_progress_monitor_reports_live_run_as_dead_2026-09-03.md`: across the
36 minutes in which Stage 2 compiled all 821 units, the monitor logged
`status=alive-no-progress … cpu_pct=0.0 rss_kb=0 tree_processes=0` continuously.
Progress had to be read from log growth and phase transitions instead.

## What to do

- **Run the bootstrap in a private worktree pinned to a commit**, not in a
  shared checkout other sessions write to. That is the only reliable fix, and it
  needs disk headroom: a full Rust target is 5.4 GB and this host had 9.5 GiB
  free at the time.
- Or serialize: no other session edits `src/**` for the duration of a run.
- Worth considering separately: the refusal message names neither which snapshot
  differed nor which files changed. Both are already computed at that point;
  printing the first few differing paths would turn a 3-run investigation into a
  one-line read.

## Confirmed 2026-09-05 22:19 — isolation makes it pass

The hypothesis was tested, not assumed. The **same command** that failed three
times in the shared checkout was run in a private worktree pinned to
`origin/main` (`82d8bb16f85`), with nothing else writing to it:

```
sh scripts/bootstrap/bootstrap-from-scratch.sh \
    --strategy=adhoc --full-bootstrap --stop-after-stage2 --mode=dynload
```

Result:

```
Stage 2: running bootstrap compiler sanity
Stage 2: proving struct receiver/runtime capability
Stage 2 admitted; stopping before Stage 3 as requested.
```

The decisive input flipped:

| input | shared checkout | pinned worktree |
|---|---|---|
| `source-inputs-before` vs `-after` | **DIFFERS (14 entries)** | **IDENTICAL** |
| `stage2-sanity.env` | `status=pass` | `status=pass` |
| `stage2-receiver.env` | `status=pass` | `status=pass` |
| verdict | `refused incomplete Stage 2 admission provenance` (exit 4) | **admitted** |

Artifacts produced: `stage3/aarch64-apple-darwin/stage2-admitted/`,
`stage2-provenance.receipt` (769 B), `stage2-sanity.receipt` (438 B), and the
139,546,712-byte Stage 2 compiler.

So the gate was never wrong and Stage 2 was never broken: the shared checkout is
simply not a valid place to bootstrap while other sessions write to `src/**`.

**Operational note.** The isolated run needs its own Rust target (5.4 GB); it
was given 17 GiB of headroom and settled at 8.7 GiB free. Symlinking
`src/compiler_rust/target` at the main checkout's target to save that space does
NOT work — the run fails immediately with `error: failed to fingerprint Rust
seed inputs`. Give the worktree a real target directory.
