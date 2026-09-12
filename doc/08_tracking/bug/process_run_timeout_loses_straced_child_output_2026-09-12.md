# `process_run_timeout` captures 0 bytes from a child that runs `strace`, and `read_file_text` cannot read a file created after the process started — together they make closure specs vacuously green

- **Filed:** 2026-09-12
- Status: OPEN (2026-09-12)
- **Found by:** L5-D (generated/deployed binary closure wave), after its own
  closure spec reported **5 of 5 scenarios passing with every measurement
  empty**.
- **Binary:** deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`.
  Tree `c7c5bef3ca3`.

## Two defects, one failure mode

### A. `app.io.process_ops.process_run_timeout` returns empty stdout AND empty stderr for a child that runs `strace`, while reporting exit code 0

The command runs correctly. Only the capture is lost, and the caller is told
nothing went wrong.

```sh
cat > /tmp/capchk.spl <<'EOF'
use app.io.process_ops.{process_run_timeout}
fn t(label: text, args: [text]):
    val (out, err, code) = process_run_timeout("sh", args, 600000)
    print "{label}: argc={args.len()} code={code} out_len={out.len()} err_len={err.len()}"
fn main():
    t("echo3", ["-c", "echo a b c"])
    t("measurer", ["scripts/perf/measure-entry-closure.shs", "check-help", "--samples", "0"])
    t("echo7", ["-c", "echo $0 $1 $2 $3 $4 $5", "a", "b", "c", "d", "e", "f"])
EOF
cd <repo root>
bin/release/aarch64-unknown-linux-gnu/simple run /tmp/capchk.spl
```

Observed:

```
echo3: argc=2 code=0 out_len=6 err_len=0
measurer: argc=4 code=0 out_len=0 err_len=0
echo7: argc=8 code=0 out_len=12 err_len=0
```

`echo7` rules out an argument-count limit. Running the identical measurer
command straight from a shell prints a 55-line report ending in a `PASS — …`
verdict, and redirecting it to a file from inside the same Simple child writes
**6,291 bytes**. So the child executes fully; `process_run_timeout` simply
returns nothing for it.

The distinguishing property is that the child invokes `strace`
(`scripts/perf/measure-entry-closure.shs` traces the measured entry with
`strace -f -e trace=openat`). A wrapper's own output around the straced command
IS captured — `sh -c "sh measurer … > F 2>&1; echo rc=$?"` returns `rc=0`
correctly — so the loss is confined to output produced under the trace.

### B. `std.io_runtime.read_file_text` returns `""` for a file created after the reading process started

The obvious workaround for A — redirect to a file, read the file back — does not
work either:

```sh
cat > /tmp/readback.spl <<'EOF'
use app.io.process_ops.{process_run_timeout}
use std.io_runtime.{read_file_text}
fn main():
    val p = "/tmp/l5d_probe.txt"
    val (_o, _e, c) = process_run_timeout("sh", ["-c", "sh \"$0\" \"$1\" --samples 0 > \"$2\" 2>&1", "scripts/perf/measure-entry-closure.shs", "check-help", p], 900000)
    print "code={c}"
    print "file_len={(read_file_text(p) ?? "").len()}"
EOF
cd <repo root>
bin/release/aarch64-unknown-linux-gnu/simple run /tmp/readback.spl
ls -l /tmp/l5d_probe.txt
```

Observed:

```
code=0
file_len=0
-rw-rw-r-- 1 yoon yoon 6291 Sep 12 15:08 /tmp/l5d_probe.txt
```

The file is on disk with 6,291 bytes and the same process reads it as empty.

## Why this is worse than a missing feature: it manufactures green

Every L5 closure spec follows the shape the wave plan prescribes — shell out to
`scripts/perf/measure-entry-closure.shs`, parse its verdict, and *skip honestly
with a printed reason if the measurer is unavailable*. Under defect A the
verdict string is always empty, which is indistinguishable from "measurer
missing", so the honest-skip branch swallows every scenario and the spec reports
success having measured nothing.

Observed exactly that, before the cause was known
(`test/05_perf/startup/check_lint_entry_closure_spec.spl`, L5-D):

```
[closure] SKIPPED check-help/default: measurer produced no verdict line (missing scripts/perf/measure-entry-closure.shs?)
[closure] SKIPPED check-help/interpreter: …
[closure] SKIPPED lint-one-file/default: …
[closure] SKIPPED lint-one-file/interpreter: …
5 examples, 0 failures
SPEC FILE VERDICT: … outcome=OK … passed=5 failed=0
```

The measurer was present and working the whole time.

**Specs this makes vacuous.** Any spec in the L5 wave that calls the measurer
through `process_run_timeout` and treats an empty verdict as a skip:
`test/05_perf/startup/check_lint_entry_closure_spec.spl` (L5-D, fixed — see
below), and by construction the sibling closure specs the wave plan asks for —
`mcp_entry_closure_spec.spl` (L5-B), `lsp_mcp_entry_closure_spec.spl` (L5-C),
`cross_lane_parse_once_spec.spl` (L5-E) and
`test_runner_entry_closure_spec.spl` (L5-G). Each should be checked against the
guard below rather than assumed clean; a passing run is not evidence here.

## Guard used, until the defects are fixed

Two changes, both in
`test/05_perf/startup/check_lint_entry_closure_spec.spl`:

1. **Route the verdict through the wrapper, not the traced child.** Redirect
   inside `sh -c` and grep the verdict back out; the wrapper's own `grep` output
   is not under the trace and is captured normally:

```
process_run_timeout("sh", [
    "-c",
    "sh \"$0\" \"$1\" --lane \"$2\" --samples 0 --verify-cold > \"$3\" 2>&1; grep -E '^(PASS|ERROR) ' \"$3\" | tail -1",
    MEASURER, entry_id, lane, log_path
], MEASURE_TIMEOUT_MS)
```

2. **Make skipping fail-closed.** Probe the producer first with
   `--list-entries`, which runs no `strace` and captures fine. If it answers,
   an empty or `ERROR` verdict is a **failure**, not a skip — a measurement that
   did not happen must never read as a pass. Only a genuinely absent or
   unrunnable producer skips.

With both in place the same spec reads real numbers and correctly fails its one
expected-red scenario.

## Not yet determined

- The mechanism of A. Plausible candidates not yet distinguished: `strace`
  attaching to the process group and the seed's pipe reader being closed or
  consumed; the tracee inheriting the pipe write end and the reader seeing EOF
  early. No `strace` of the seed itself has been taken.
- Whether A affects any straced child or only one that traces a `simple`
  binary (i.e. a nested seed process).
- The mechanism of B, and whether it is a cached `stat`, a memoised read, or an
  mmap path that captured the file's absence at process start. A file that
  already existed when the process started reads fine — that is how the same
  spec reads `src/app/cli/check_entry.spl` successfully in another scenario.
- Whether `process_run` (no timeout) behaves the same as `process_run_timeout`.
  Only the timeout form was measured.
