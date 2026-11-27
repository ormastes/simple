# Test runner spec child loses its mode pins (no examples executed) — 2026-11-14

**Status:** FIXED (branch `work/caret-red-specs-20261114`).

## Symptom
`bin/simple test <spec>` reported `ERROR — 0 examples executed ... produced no
SPEC FILE VERDICT line` (`reason=no-examples-executed`) for `fn main`-style
specs WITHOUT a `"""` docstring header, e.g. the Caret ink specs
`test/01_unit/app/llm_caret/claude_full/ink/events/{click,input,terminal,terminal_focus}_event_spec.spl`
and `ink/log_update_spec.spl`. The examples themselves passed.

## Root cause
`203f43bc0c6` (2026-11-12) added the `SIMPLE_TEST_CHILD_ENV_SCRUB` marker and
made `_process_run_bounded_raw` (and the other raw facades) scrub
`SIMPLE_EXECUTION_MODE`/`SIMPLE_RUNTIME_MODE` + the marker whenever the marker
is set. The single-file runners (`src/app/test_runner_new/test_runner_single.spl:1731`,
`src/lib/nogc_sync_mut/test_runner/test_runner_single.spl:215`) set the marker
and then spawned their spec child through that SAME scrubbing helper, so the
spec child got neither pins nor marker. Unpinned, `simple run` picks the JIT:
the JIT runs `main` and the seed prints no `SPEC FILE VERDICT`. Specs with a
docstring were masked: the docstring counts as a skipped top-level statement,
which demotes the JIT to the interpreter, which does print the verdict.
Side effect: interpreter-only visibility errors were also hidden on these lanes
(see `interpreter_lane_private_fn_imports_imap_font_2026-11-14.md`).

## Fix
`std.nogc_sync_mut.io.process_ops.process_run_bounded_spec_child` — the
unscrubbed bounded run; `_process_run_bounded_raw` now wraps it with the scrub.
Both single-file runners spawn their spec child through it.

## Specs
- Reproducer: `test/01_unit/app/test_runner_new/spec_child_receives_mode_pins_spec.spl`
  (docstring-less `fn main` spec asserting the pins reach the child under `simple test`).
- Generalization: `test/01_unit/lib/nogc_sync_mut/io/process_spec_child_env_pins_spec.spl`
  (spec-child spawn keeps pins+marker; bounded and unbounded facades still scrub;
  caller env restored after a scrubbing spawn).
