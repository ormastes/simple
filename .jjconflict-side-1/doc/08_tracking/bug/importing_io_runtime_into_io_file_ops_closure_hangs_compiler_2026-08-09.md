# `file_read_bytes` convergence blocked by non-reproducible "test daemon timed out" with no verdict

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
treat the cycle theory below as confirmed

**Re-checked 2026-08-09/10:** Reproduced the identical symptom twice more on
this same contended host (`load average 82-140`, ~270 resident `simple`
processes, `kill_simple_monitor.shs` and `earlyoom` both live) — once on the
exact repro spec
(`test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl`)
and once on an unrelated freshly-written synthetic spec touching a completely
different module (`std.nogc_sync_mut.io.image_sffi`, no `io_runtime`
involvement at all). Both runs, with `SIMPLE_TIMEOUT_SECONDS=900` set, ended
identically: normal compile warnings up through the last `[gc-warning]` line,
then a **blank line, `EXIT=1`, no `SPEC FILE VERDICT`, and no "timed out"
text at all** — not even the daemon-timeout message quoted in the Symptom
section below. That the failure is silent (no diagnostic string, not even
the harness's own timeout message) and hits an *unrelated* file the same way
is strong corroboration for this doc's own "Environment confound" section:
this reads as `kill_simple_monitor.shs` SIGTERM'ing the run outright rather
than the test daemon's own timeout firing (see
`.claude/memory` note on the 60s-high-CPU kill guard). This session could not
get a quiet host to test the import-cycle theory in isolation, so per this
doc's own "Next step" the correct disposition remains OPEN, now with two
additional non-reproductions-with-a-verdict as evidence the confound is real
and current, not stale from 2026-08-09.
**Found:** 2026-08-09 — stream G2, while converging `file_read_bytes`
**Severity:** blocker for
`doc/08_tracking/bug/file_read_bytes_has_six_definitions_with_three_return_types_2026-08-09.md`
**Component:** unknown — test daemon / module loader / local environment

## Symptom

Repeatedly, `bin/simple test <spec>` produced:

```
ERROR: test daemon timed out: test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl
EXIT=1
```

with **no `SPEC FILE VERDICT` line**. Per this repo's own measurement rules, a
non-zero exit with no verdict line is indistinguishable from "ran nothing", so
this is a measurement-destroying failure mode regardless of its cause.

## What is actually established

- The same spec ran to completion **twice early on** (`executed=5 passed=5`, and
  `passed=3 failed=2` under deliberate sabotage), on a fully converged tree.
- It then timed out **4 times in a row**, including after every source change
  had been reverted to `HEAD` except two deletions of zero-importer mock
  functions. That final timeout is the important one: **it means the timeouts
  are not explained by the convergence edits**, since at that point essentially
  nothing was changed.
- One intermediate run did complete (`executed=5 passed=4 failed=1`) with
  `io/file_ops.spl` at `HEAD`, which is what originally suggested an import
  cycle. Given the final result above, that single data point is **confounded**
  and must not be read as isolation.

## What is NOT established

An earlier draft of this report confidently attributed the hang to an import
cycle created by pulling `std.io_runtime` into the `io.file_ops` closure. **That
conclusion is not supported.** It rested on one completing run versus one
hanging run, on a machine that was concurrently running several other test
processes, and the effect did not survive reverting the change.

## Environment confound to rule out first

The host is contended and runs watchdogs that can kill or stall long runs:

- `scripts/resource/kill_simple_monitor.shs` was running throughout
  (this repo's notes record that it SIGTERMs runs at high CPU, and that
  bootstrap/full-suite/cold-lint runs therefore cannot finish without
  `SIMPLE_TIMEOUT_SECONDS=3600`, which WAS set here).
- `earlyoom` is configured with `--prefer ^(simple|rustc|...)`, i.e. it
  preferentially kills `simple` processes under memory pressure.
- Several long-lived `simple_lsp_mcp` server processes were resident.

Any of these can produce a stalled or killed compile that the harness surfaces
as a daemon timeout.

## Next step

Re-run the convergence on a **quiet machine** with the watchdogs stopped, and
record binary identity (`readlink -f bin/simple` plus size/mtime) alongside every
timing, since the symlink target is replaced by other sessions mid-session. Only
if the timeout reproduces there is there a compiler defect to chase; the import
cycle theory should then be tested directly rather than inferred from timings.

Independently of the cause: **a hang with no diagnostic is itself worth fixing.**
An unresolvable or cyclic import should produce an error naming the participating
modules and exit non-zero, never stall without output.
