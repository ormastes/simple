# Spec exits 255 with no example output: 60s test-runner timeout, not a parse error (OPEN)

**Date:** 2026-08-01
**Status:** OPEN — root cause PROVEN; fix is a policy/perf decision, not a one-liner
**Spec:** `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`
**Found by:** commit `e9f1469e5d3` (left unidentified at the time)

## Symptom

```
$ simple test test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl
# ... ~1900 lines of unrelated warnings ...
EXIT=255      # no "N examples, M failures" line anywhere
```

Proven pre-existing by the finding lane: they deleted their own added block and
re-ran — still 255 — and a control spec was clean.

## Root cause (PROVEN)

**The spec takes longer than the test runner's 60-second default per-spec
timeout. The runner SIGKILLs the child, the bounded output drain discards the
child's buffered stdout, and the killed-child path returns `-1`, which the shell
reports as 255.**

The chain, with file:line:

1. `src/lib/nogc_sync_mut/test_runner/test_config.spl:76`
   `config_int_field("timeout_seconds", "60", 1)` — **default 60s per spec.**
2. `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:141`
   `val timeout_ms = options.timeout * 1000` → passed to
   `process_run_with_limits_bounded(...)` at line 152.
3. `src/compiler_rust/compiler/src/interpreter_extern/system.rs:140-153`
   on expiry sets `timed_out = true` and `libc::kill(-pid, SIGKILL)` — the whole
   process **group**, so the child dies without flushing.
4. `system.rs:158-160` — `let bounded_drain = timed_out || aborted;` the drain is
   truncated, **which is why zero example output survives**.
5. `system.rs:161-166` — appends `"Process timed out"` to stderr.
6. `system.rs:170-174` — returns **`-1`** on timeout, surfacing as shell **255**.

### Decisive evidence

Same file, same binary, only the timeout changed:

| invocation | result |
|---|---|
| `simple test <spec>` (default 60s) | **exit 255**, zero example output, `Process timed out` buried in stderr |
| `simple test --timeout 600 <spec>` | **`15 examples, 2 failures`, exit 1**, no timeout message |
| `simple run <spec>` (JIT, no timeout) | **`15 examples, 2 failures`, exit 0** |

The spec parses, loads, and executes all 15 examples whenever it is given time.

## What it is NOT — hypotheses checked and excluded

The tasking's four leading hypotheses are all **ruled out** by the fact that the
file reaches and runs all 15 examples under both `run` and `test --timeout 600`:

- **NOT a parse error.** The parser accepts the file end to end.
- **NOT an import failure / bare-name collision.** All ten `_driver_*` symbols
  imported at lines 8-14 resolve; each is defined exactly once in
  `src/compiler/80.driver/driver_source_loading.spl` (`fn <name>(` count == 1 for
  all ten). The widened `warn_duplicate_private_signatures` detector
  (`59c26310533`) fires only on unrelated pre-existing colliders (`u32_to_bytes`,
  `u64_to_bytes`, `write_file`, `shell_output`, `update_test_database`, …) — none
  are used by this spec.
- **NOT an eager-import cycle** yielding a silent empty export dict
  (`module_loader.rs:773`) — the imported functions returned real values.
- **NOT a soft-keyword clash** (`literal`, `gen`, `val`, `def`, `exists`,
  `actor`, `assert`, `join`) and **not** the inline-`match`-in-arg-list defect
  fixed by `8fdc21c67b5` — the spec contains no inline `match`, and it parses.

Also excluded: an **isolation probe** that imports the compiler driver into a
one-example spec (`use compiler.driver.driver_source_loading.{...}`) runs clean
through `simple test` in well under 60s. So importing the driver is not itself
the trigger — the cost is the spec's own 15 examples, which read and scan ~20
large compiler source files (`rt_file_read_text` + repeated `.find()`/
`.contains()`/`.index_of()` full-text scans) under the **tree-walk interpreter**
that `test` hard-defaults to.

### Note on the brace-interpolation red herring

The spec's own comment at lines 124-127 documents a *different, already-fixed*
cause of the identical signature ("a bare `{}` in an ordinary string literal is
parsed as an empty interpolation and kills the whole spec file at parse time
(observed: runner exits 255 with no example output)"). That mitigation is still
in place and correct — lines 128/153 use raw strings, lines 167/168/278
concatenate `"{"` by hand. Measured behaviour of the two forms today:

| literal in an ordinary (non-raw) string | behaviour |
|---|---|
| `"a.b.{run_test_cli}"` — single identifier | **interpolates** (printed `a.b.0`) |
| `"a.b.{run_a, test_b, test_c}"` — comma form | stays literal, exit 0 |

So line 203's un-raw `"...{run_test_json_wrapper, test_json_requested,
test_json_worker_requested}"` is the comma form and is **not** a parse hazard
today. Two distinct mechanisms produce the same "255 + no output" signature; the
comment made the parse-time one look like the live cause, and it is not.

## The real defect

**A timeout kill is unattributable at the exit-code level.** `-1`/255 with a
truncated output drain is indistinguishable from a crash or a load abort, and
the one clue — the literal string `Process timed out` — lands on stderr *after
~1900 lines of unrelated `[compiler_cross_module_private_symbol_collision]` and
`[gc-warning]` noise*, where two separate lanes missed it. The runner already
has a timeout classification (`test_runner_execute.spl:62`,
`case "timeout": "Timed out under resource limits"`) but this path does not
reach it.

## Recommendation — do NOT weaken the spec

The spec asserts real contracts and stays as-is. Its 2 remaining failures under
a sufficient timeout are the **extractor defect it already documents in its own
header** (lines 17-28: `.find()` returns a BYTE offset while `.substring()`
takes a CHARACTER offset, shifting one slice by 4 chars) — pre-existing,
acknowledged, tracked in
`doc/08_tracking/bug/text_find_native_exposure_audit_2026-07-31.md`. Not
addressed here.

Actionable follow-ups, priority order:

1. **Make a timeout kill self-identifying.** Emit a distinct exit code (or a
   `Results:`-adjacent `TIMEOUT <spec> after Ns` line on stdout) so 255 is never
   confused with a parse/load abort. This is the highest-value fix: it is what
   cost `e9f1469e5d3` and this lane an investigation each.
2. **Preserve partial output on timeout.** `system.rs:158` truncates the drain
   precisely when diagnosis needs it most; emitting whatever examples completed
   would have identified this in seconds.
3. **Add a per-spec timeout override.** There is an `--only-slow` *filter*
   (`test_runner_args.spl:278`) but no per-spec timeout annotation, so a
   legitimately slow spec has no way to declare its budget and is permanently
   red in a default run. Either add one, or mark this spec slow and exclude it
   from the default lane.
4. **Perf:** the spec's full-text `.find()`/`.contains()` scans over ~20 large
   compiler sources are quadratic-ish under the tree-walk interpreter. Making
   those scans cheaper would put the spec back under 60s without any policy
   change.

## Reproduction

```bash
# 255, no example output  (default 60s timeout)
src/compiler_rust/target/bootstrap/simple test \
  test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl

# 15 examples, 2 failures, exit 1  (proves it is only the timeout)
src/compiler_rust/target/bootstrap/simple test --timeout 600 \
  test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl
```

## References

- `src/compiler_rust/compiler/src/interpreter_extern/system.rs:140-175`
- `src/lib/nogc_sync_mut/test_runner/test_config.spl:76`
- `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:141,152,62`
- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`
- `doc/08_tracking/bug/text_find_native_exposure_audit_2026-07-31.md`
- `doc/08_tracking/bug/compiler_cross_module_private_symbol_collision_2026-06-16.md`
