# `print` drops its newline under native-build only

**Status:** FIXED in `35b22b6aedf` (original focused fix `8cef6333ac8`)
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

## Triage 2026-09-13

Attempted to re-verify with a minimal 3-print probe via
`bin/simple native-build --entry <probe> --output <bin>`. The build itself
fails before reaching link/run:

```
error: semantic: unknown extern function: rt_env_vars
error: native-build worker exited with code 1
```

This is a different, more upstream defect than the one this record
describes (native-build cannot currently produce ANY artifact on this
worktree, not even a trivial 3-print program), so the specific
newline-dropping symptom could not be re-exercised. Binary: `bin/simple` =
Rust seed `bin/release/aarch64-unknown-linux-gnu/simple` (symlinked from the
shared main worktree), sha256 `3d120a6f9ab5`. Left OPEN; the native-build
`rt_env_vars` breakage blocking this re-check is not filed separately here
for time — flagged for whoever next touches native-build.

## Resolution and re-verification 2026-09-14

The focused fix is present in the current pure-Simple MIR lowerer:
`print` routes to `rt_println`, while the deliberately non-newline internal
`_cli_eprint` helper remains on `rt_print`. The fix originally landed as
`8cef6333ac8` and is carried by the current history through `35b22b6aedf`.
Its Stage-2 admission oracle observed three `print` calls as three lines after
the change, directly covering the reported native-output failure.

The repository also has a stronger byte-for-byte differential gate,
`scripts/check/check-native-print-stdout-oracle.shs`, with four positive
fixtures and a deliberately wrong negative control. A Windows re-run using
the deployed seed (SHA-256
`6094DCAE291AA984973CCD681F956E67A7A60543AB99F76A29313FBBFDEE96D1`)
was blocked before artifact production by SCV inventory publication
(`compile-event-journal-missing`, then
`git-event-apply:inventory-publication-failed` on the prescribed cold-init
retry). That is an admission/inventory failure, not a recurrence of newline
loss. Implementation status is therefore fixed; refreshing the differential
gate on the next admitted native candidate remains deployment verification.
