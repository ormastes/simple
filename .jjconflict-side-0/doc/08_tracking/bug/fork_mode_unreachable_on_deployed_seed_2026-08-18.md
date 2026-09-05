# Fork mode (`--fork`) is unreachable on the deployed seed — its SFFI bridge is absent from the binary

- **Filed:** 2026-08-18 — **Severity:** MEDIUM — **Status:** OPEN
- **Component:** `src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl`,
  `src/runtime/runtime_fork.c`
- **Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple`
  (Rust bootstrap seed; prints the seed warning banner)

## Symptom

`test_runner_fork.spl:37-43` declares seven `extern fn rt_fork_*` symbols and
`:46` `rt_cli_run_file`. The deployed binary contains **none** of the former:

```
$ B=$(readlink -f bin/simple)
$ strings -a $B | grep -c 'rt_fork'          # 0
$ strings -a $B | grep -c 'rt_cli_run_file'  # 12   <-- control
$ strings -a $B | grep -c 'rt_string_concat' # 5    <-- control
$ nm $B | grep -c rt_fork_                   # 0
$ nm -D $B | grep -c rt_fork_                # 0
```

Both controls are non-empty, so this is not a stripped-binary artefact: the
`rt_fork*` bridge from `src/runtime/runtime_fork.c` was never linked into this
seed. `runtime_fork.c` is listed in the pure-Simple backend's runtime source
set (`src/compiler/70.backend/backend/runtime_compiler.spl:284,301`) and in the
Stage 4 fork-provider archive path (`llvm_native_link.spl:905-921`) — i.e. the
**native** link brings it in, but the seed does not.

Consequence: `bin/simple test <dir> --fork` cannot execute the fork path on the
default tooling binary, so every fork-mode claim is currently unverifiable on
this host.

## What the attempted run produced (verbatim, no results line)

Two fixtures (a deliberately-recursing spec plus a trivially-passing follow-up)
run as `bin/simple test . --fork`:

```
lines=364
grep -nE "Results:|example|CRASHED|TERMINATED|TIMEOUT|NOT EXECUTED|mode:|rt_fork" fork.log
(no matches)
```

364 lines, all lint warnings, **zero** result lines. That is the already-filed
silent-green defect
(`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`),
so the run is INCONCLUSIVE and is not evidence either way about fork mode.

## Secondary finding: no crash fixture exists that actually crashes

The obvious crash fixture does not crash — the interpreter has a recursion
guard, so unbounded recursion is reported as an ordinary failing example, not a
signal death:

```
$ bin/simple run a_crash_spec.spl   # RC=1
  ✗ segfaults
    stack overflow: recursion depth 1000 exceeded limit 1000 in function 'boom'
1 example, 1 failure
SPEC FILE VERDICT: a_crash_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0
```

So the "no crash fixture" gap recorded in `.spipe/unstable_test_mode/state.md`
is sharper than it reads: a fixture that produces a genuine SIGSEGV/SIGABRT
from `.spl` source has not been found, and the classification code in
`classify_fork_exit` (`test_runner_fork.spl:73-94`) therefore has **no
execution evidence at all** — only source review.

## Unblock conditions

1. Link `runtime_fork.c` into the seed, or deploy a self-hosted `bin/simple`
   whose native link already includes the fork provider archive.
2. Fix the silent-green defect so a `--fork` run emits a results line.
3. Author a fixture that genuinely dies by signal (likely needs an SFFI call
   into `abort()`/a null deref, not pure `.spl`).

Until all three hold, treat fork mode as source-reviewed and unexercised.

## Related

`doc/05_design/lib/test_runner/fork_mode_is_not_fresh_process_per_unit.md` —
why COW-fork is crash containment but not the fresh-process-per-unit guarantee
unstable mode is defined as, and the exact change required.
