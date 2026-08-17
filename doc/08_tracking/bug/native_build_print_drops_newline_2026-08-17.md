# `print` drops its newline under native-build only

**Status:** OPEN (P2)
**Filed:** 2026-08-17
**Component:** native-build (AOT) `print` lowering
**Class:** engine divergence — output differs from both other engines

## Symptom

Three consecutive `print` calls in a native-built binary emit one run-together
line:

```
got=...eq=truelen=1
```

The same program under `SIMPLE_EXECUTION_MODE=interpret` and `=jit` emits three
separate lines. So the newline is dropped in the AOT lane only.

## Why it matters beyond cosmetics

Every gate and guard in this repo reads a **verdict line** from stdout, and
several parse per-line markers. A lane that concatenates its output silently
defeats a `grep '^Results:'` or a line-oriented scan — the data is present but
unparseable, which reads as "no verdict" rather than "wrong output". Given how
much of today's evidence collection turned on an absent `Results:` line, an
output lane that eats newlines is a false-signal generator.

## Reproduction

Build any program with three `print` statements via `bin/simple native-build`,
run the binary, and compare with the two pinned engine arms:

```
SIMPLE_EXECUTION_MODE=interpret bin/simple run <probe>   # three lines
SIMPLE_EXECUTION_MODE=jit       bin/simple run <probe>   # three lines
./<native binary>                                        # one line
```

Read rc into a variable on the line AFTER the command, never through a pipe.

## Not verified

- Whether `println`-style or explicit `"\n"` output is affected the same way.
- Whether the newline is lost at lowering or in the runtime's write path.
- Whether stderr diverges identically.
- Which native backend arms are affected (only one was exercised).

Found incidentally while reproducing
`native_empty_dict_text_value_sigsegv_2026-07-20` — the run-together line is what
made the wrong value visible in the first place. Filed separately because it is a
distinct defect in a different subsystem from that row.
