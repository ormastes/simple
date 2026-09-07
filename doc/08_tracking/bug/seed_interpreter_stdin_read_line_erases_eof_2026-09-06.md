# Seed interpreter's `Stdin.read_line()` erases EOF into `Ok("")`

Date: 2026-09-06
Status: FIXED IN SOURCE — awaiting a seed deploy (see "Fix" below)
Area: `src/compiler_rust/compiler/src/interpreter_extern/io/input.rs` (Rust seed only)

## Fix (2026-09-06)

`input()` now maps the EOF `None` to `Value::Nil` instead of
`unwrap_or_default()`-ing it into `""`, matching the C runtime and the extern's
declared `-> text?` contract.

Verified with a privately-built binary (`bin/simple` deliberately NOT replaced —
other sessions are using it):

| case | before | after |
|---|---|---|
| `run main.spl < /dev/null` | exit 124, 12.3 MB | **exit 0, 2 bytes** |
| `printf 'hello\n\n/exit\n'` | — | exit 0, 53 bytes, blank line still yields a fresh prompt |

So both directions hold: EOF terminates, and a genuine blank line is still a
blank line.

**Still required: someone must actually build and deploy the fixed seed.** The
two `# ponytail:` ceilings in `chat_tui.spl` and `cs_main.spl` are now provably
obsolete — EOF reaches the pre-existing `else: running = false` branches
correctly — but they were deliberately left in place, because deleting them
before the fixed seed ships would break caret for every host still on the
current binary. Delete them in the same change that deploys the seed.

## Summary

On the Rust bootstrap seed, `Stdin.read_line()` returns `Ok("")` at end of
input — the same value a genuine blank line produces. EOF is therefore
**indistinguishable from a blank line**, and no caller can terminate a read loop
correctly.

The C runtime does NOT have this defect: `src/runtime/runtime_native.c:2262`
correctly returns `NULL` at EOF. This is a seed-interpreter-only divergence from
the documented `Stdin.read_line()` contract.

## Root cause

`interpreter_extern/io/input.rs`, fn `input` (the seed interpreter's
`rt_stdin_read_line` stub):

```rust
.lines().next().transpose()?.unwrap_or_default()
```

`.next()` yields `None` at EOF. `.unwrap_or_default()` converts that `None` into
`""` before it can be mapped to `nil`, destroying the only EOF signal.

## Observed impact

`src/app/llm_caret/chat_tui.spl` `run_chat_plain` and `src/app/llm_caret/cs_main.spl`
`cs_run` both contain a correct `else: running = false` branch for a `nil` read.
That branch **can never execute on the seed**, so:

```
timeout 120 bin/simple run src/app/llm_caret/main.spl < /dev/null
  -> EXIT=124 (never terminates)
  -> 12.3 MB of stdout, entirely repeated "> " prompts
```

A program that should exit instantly instead spins until killed, emitting
unbounded output. On a long-lived host that is a disk-fill risk.

## Mitigation applied (not a fix)

Because the adapter genuinely cannot distinguish the two cases on this runtime,
the EOF decision could not be pushed down to the IO adapter where it belongs.
Both loops instead gained a bounded consecutive-empty-read ceiling
(`_PLAIN_MAX_CONSECUTIVE_EMPTY_READS` / `_CS_MAX_CONSECUTIVE_EMPTY_READS`, 1000),
reset by any non-blank line, and each is tagged `# ponytail:` naming this bug as
the upgrade path. Post-mitigation the same command exits 0 having written 2,000
bytes instead of 12.3 MB, and blank lines still behave correctly (verified with
`printf '\n\n/exit\n'`: both blank lines yield fresh prompts, `/exit` exits).

The ceiling is a workaround for a runtime defect. **The real fix is in
`input.rs`**: return `None`/nil at EOF so it matches the C runtime and the
`Stdin.read_line()` contract, after which both ceilings should be deleted and
the pre-existing `else: running = false` branches will do the right thing on
their own.

## Related, separate, also open

Probing `Stdin.new().read_line()` directly from a small `.spl` program **aborts
the runtime**:

```
thread caused non-unwinding panic. aborting.
  ... rt_value_raw_i64
[crash] report written to .simple/logs/crash_<pid>.log
-> SIGABRT (exit 134)
```

Reproduces content-independently — empty stdin and blank-line stdin both crash —
under both JIT and forced `--backend interpreter`, on the seed only. Caret's own
production path does not crash, so this is reachable only by certain call shapes.
Not diagnosed further; recorded here because it blocked direct measurement of the
EOF semantics above and had to be worked around by instrumenting the production
path instead.

## Verify

```
timeout 120 bin/simple run src/app/llm_caret/main.spl < /dev/null; echo "EXIT=$?"
```

Binary measured: `bin/release/aarch64-unknown-linux-gnu/simple`,
`Simple Language v1.0.0-rc.1` (Rust bootstrap seed).
Not verified on a self-hosted binary — none exists on this host.
