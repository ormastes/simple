# In-development tag sweep — slice 2: system trees (`test/03_system/`, `test/system/`)

**Date:** 2026-08-23
**Slice:** `test/03_system/` + its mirror `test/system/`
**Tag mechanism:** `# @tag:in-development` (`970920e02cd`, `src/lib/nogc_sync_mut/spec/in_development.spl`)
**Design:** `doc/05_design/app/testing/in_development_tag.md`
**Worktree:** `/mnt/fast/wt-tagsweep-system` at `origin/main` `21fb80be31e`
**Binary:** deployed seed `bin/release/x86_64-unknown-linux-gnu/simple` (`v1.0.0-RC`)

## Verdict up front

**0 specs tagged.** The sweep did not reach the point where tagging any spec
would have been evidence-based, and tagging without that evidence is exactly
the failure mode the tag exists to prevent. What this slice produced instead
is three findings about the *measurement apparatus* — two of which silently
manufacture false verdicts that any sweep lane reading the conventional
`Results:` line would have believed.

## Counts

| quantity | value |
|---|---|
| specs in slice (`find -name '*_spec.spl'`) | **5,323** (`test/03_system` 3,478 + `test/system` 1,858) |
| specs actually executed with a trustworthy verdict | **132** (2.5%) |
| of those: passed | 130 |
| of those: failed | **2** |
| tagged `in-development` | **0** |
| left RED (see below) | 2 |
| environmental (candidate pool, not failure-confirmed) | see census below |
| inconclusive / not measured | **5,191** |

The brief quoted 3,465 / 1,858. The measured counts are 3,478 / 1,858; the
`test/03_system` figure is 13 higher.

## Finding 1 — the `@cover` preflight gate manufactures phantom failures

A plain `bin/simple test test/03_system/feature` returns:

```
Results: 587 total, 0 passed, 587 failed
Time:    0ms
[MEM] AFTER_RUN_0_files: ...
```

**Zero specs executed.** The 587 "failures" are system specs missing a
`# @cover src/... 80%` header, rejected by a preflight gate
(`src/app/test_runner_new/test_runner_main.spl:268-282`) that aborts the run
and reports each missing annotation as a failed test. `test/03_system/infrastructure`
gives the same shape with 51.

This matters beyond this slice. The repo convention is that the `Results:`
line is the authoritative verdict — and it is, *for verdicts*. It is **not**
proof that anything ran. A lane trusting it alone here would report 638+
phantom failures and could tag healthy specs as in-development.

**Cross-check that distinguishes the two cases:** `Files: N discovered, N executed`,
`AFTER_RUN_<n>_files`, and `Time:`. A gate abort shows `0`/`0ms` while still
printing a fully-formed `Results:` line.

**Bypass:** `--no-cover-check` (`test_runner_args.spl:484`).

The `@cover`-missing population (638+ system specs and counting) is real debt,
but it is **harness/annotation debt, not unfinished feature work**. Nothing in
it may be tagged `in-development`.

## Finding 2 — the resource watchdog truncates runs to the first 20 specs

With the cover gate bypassed, both lanes stopped after exactly 20 tests, `rc=42`:

```
GRACEFUL SHUTDOWN INITIATED
Reason: cpu=99.0%>75.0% AND memory=88.0%>75.0%
Completed tests: 20
```

This is the runner's resource self-protection (`resource_limit_pct` default 75,
checked every 20 tests at `test_runner_main.spl:369,412`; exit 42 =
`EXIT_RESOURCE_SHUTDOWN`, `shutdown.spl:15`). It samples **system-wide** CPU and
memory, which on a shared box is dominated by other agents' load — so it does
not throttle the sweep's own footprint, it refuses to run the tree at all while
the box is busy. A lane that did not notice would silently sample only the
first 20 specs of each directory and call the rest green.

**Bypass:** `--no-self-protect`. **Use with care** — see finding 3.

## Finding 3 — `simple` is the box's designated OOM victim

With self-protection disabled, the run was killed externally at 26 specs,
`rc=143` (SIGTERM):

```
/usr/bin/earlyoom -r 3600 --prefer ^(simple|rustc|cc1|cc1plus|lto1|collect2|qemu-system|ld)
                          --avoid ^(claude|codex|gemini|node|sshd|...)$
```

`earlyoom` **preferentially** SIGTERMs `simple` processes, and the box was at
109/125 GB used. So findings 2 and 3 are two halves of one constraint: the
runner's watchdog is right that this box cannot host a 5,323-spec sweep, and
disabling it just moves the kill from a graceful checkpoint to an external
SIGTERM. This is an environmental limit on *measuring* the tree, and it is the
direct reason 97.5% of the slice is unmeasured.

The sweep was **paused by the coordinator** at ~13 GB free to protect a
concurrent stage1 build, and was not resumed within this session. Nothing of
this lane was running at pause time.

## Left RED — not tagged, and why

Both reproduce **identically across two independent runs**, so both are real
and deterministic, not flakes.

| spec | observed | why NOT tagged |
|---|---|---|
| `test/03_system/feature/scilib/ndarray_sort_spec.spl` | `4 passed, 1 failed, 1 skipped` | Which of the 6 examples fails is **not recoverable from sweep output** — the log carries only `Error: Process exited with code 1`. The file docstring says it underpins "later DataFrame sort/groupby work", which *suggests* unfinished feature, but a docstring is not evidence about the failing assertion. Tagging on a guess is precisely the misuse the tag forbids. |
| `test/03_system/feature/scilib/ndarray_concat_stack_spec.spl` | `5 passed, 1 failed, 1 skipped` | Same. Docstring says "axis-general concatenate/stack is a later phase" — again suggestive, not evidence. |

**Unblock for both:** run each explicitly (`bin/simple test <path>`, which per
the tag design gives an honest red with per-example detail) and read the failing
example. Only then is a tag-vs-bug-record decision defensible. Both target
`src/lib/nogc_async_mut/ndarray/mod.spl` per their `@cover` headers.

## Environmental candidates — census, NOT failure-confirmed

Environmental unavailability is **not** in-development and must not carry the
tag. Because only 2.5% of the slice ran, this is a *static exposure census*
(files mentioning each marker), not a list of confirmed environmental skips:

| marker | files in slice |
|---|---|
| `qemu` / `QEMU` | 349 |
| `nvidia` / `cuda` / `CUDA` / `vulkan` | 167 |
| `localhost` / `127.0.0.1` / `http://` | 73 |
| `gdb` / `openocd` / `/dev/tty` | 33 |
| `DISPLAY` / `X11` / `wayland` / `SDL_` | 18 |
| `CLAUDECODE` / `*_API_KEY` / `api_key` | 9 |

**On the tag question the brief asked:** the existing `@tag:qemu` convention is
present but tiny — 3 occurrences across `test/03_system`, against 349 files that
mention QEMU. Existing tag usage in this tree is dominated by `@tag:system` (104)
and `@tag:gui` (12). So `@tag:qemu` is a real convention but is **nowhere near
applied**, and there is no existing tag at all for GPU, network, serial-port, or
live-API dependence. Recommendation: these need a **host-capability tag family**
(the `skip()`/`skip_it()` channel already carries the right *semantics* per
`in_development.spl` — "the host cannot run this" — but it is a runtime call,
not a greppable file-level declaration). Do not stretch `in-development` to
cover any of it: the design doc rules this out explicitly, since `skip` is a
claim about the host and `in-development` is a claim about the code under test.

## Update — apparatus fixes landed by peer lanes (2026-08-23)

**Finding 1 is fixed upstream.** A peer session landed `af3c30ecdaa` (spec
`b5d9231471a`, record `818c6c44600`): `print_summary` now **refuses to emit
`Results:`/`Time:`/a verdict** when a run aborted before executing anything,
printing an **`ABORTED BEFORE EXECUTION`** block instead, gated by a new
predicate `run_aborted_before_execution()`.

- **Invocation is unchanged** — keep passing `--no-cover-check`.
- **New reading rule:** on `ABORTED BEFORE EXECUTION` the counts are
  **UNKNOWN, not failures**. Never classify or tag a spec from such a run.
- The same treatment has been requested for the finding-2 watchdog path
  (`GRACEFUL SHUTDOWN`, `Completed tests: N`, rc=42), plus stating the
  truncation count plainly and measuring the runner's **own process tree**
  rather than system-wide CPU/memory — the latter is precisely what aborted
  this lane's runs, since the load was other lanes'.
- **This only helps on a rebuilt binary.** The seed deployed for this sweep
  predates the fix, so the tells recorded above (`Time: 0ms`,
  `AFTER_RUN_0_files`, no `PASS`/`FAIL` lines, rc=3 / rc=42, `Completed tests`
  far below the unit count) remain the practical check until a redeploy.

## Cross-slice signal: the bar for tagging should stay high

Slice 1 (unit tree) executed 50 specs and found 2 failures. **Neither was
in-development**: one was spec rot calling a renamed function, the other was
contamination from another lane's uncommitted edits. Combined with this slice's
2 unclassified reds, the running total is **4 real failures observed across both
slices, 0 confirmed as unfinished feature work**. That is a strong argument that
a bulk-tag pass over these trees would mostly mislabel real defects, and it is
why this slice's deliverable is the left-red and environmental lists rather than
a tagged count.

## Method (reproducible)

```sh
git worktree add --detach /mnt/fast/wt-tagsweep-system origin/main
# deploy seed into the worktree so the sweep cannot disturb other lanes
SIMPLE_TIMEOUT_SECONDS=0 \
  bin/simple test --no-cover-check --no-self-protect --max-workers=1 <paths...>
```

Runner: `/mnt/fast/tagsweep/chunk_lane.sh` — kill-resilient, chunks the spec
list 100 files at a time, harvests `PASS`/`FAIL` lines after every chunk into a
cumulative `measured/all.txt`, and re-queues only unmeasured specs, so an
earlyoom SIGTERM costs at most one chunk. Set to `--max-workers=1` per the
coordinator's guidance for resumption. Resume gate: free memory > 30 GB.

Verdicts were taken from `PASS`/`FAIL` per-file lines, never from `$?` — an
early probe on `test/03_system/coverage` returned `rc=1` while printing
`Results: 126 total, 126 passed, 0 failed` / `All tests passed!`, the non-zero
coming from a post-run `error[E1002]: function 'runtime_file_rename' not found`
during DB write.

## What a resumed lane should do

1. Resume `chunk_lane.sh` when free memory > 30 GB. ~53 chunks/lane remain.
2. Classify each real failure by running it **explicitly** for per-example detail.
3. Tag only genuinely-unfinished feature work, twins in both mirror trees
   together (`test/03_system/X` and `test/system/X`) or
   `scripts/check/check-test-tree-divergence.shs` will fail.
4. Leave regressions and specs correctly asserting a defect RED with a bug record.
