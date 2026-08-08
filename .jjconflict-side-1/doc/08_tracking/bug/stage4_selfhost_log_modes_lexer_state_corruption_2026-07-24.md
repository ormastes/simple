# Stage 4 self-host corrupts lexer state at `log_modes.spl`

- **Status:** open; original `log_modes` boundary cleared, exact-current full CLI blocked later
- **Severity:** high
- **First observed:** 2026-07-24 on macOS arm64
- **Source revision:** `719f610e3c` plus documentation-only checkpoint

## Reproduction

An isolated, non-deployed bootstrap was run once:

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/wm-integration-current-cli \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```

The worktree-local Rust seed/runtime built successfully. Stage 2 and Stage 3
both passed bootstrap compiler sanity. The verified Stage 3 compiler then
failed Stage 4 while parsing
`src/lib/nogc_async_mut/cli/log_modes.spl`.

Evidence:

- Stage 2 SHA-256:
  `b2dbac94d70248a6fafb182b4f9d1401c1ec50e2c47558725783c579cc4377b8`
- Stage 3 SHA-256:
  `23f7ccf3b3deec27e4d24e23847799f45d3eb05c1047596b0853f4a5adc926be`
- Failure log:
  `build/wm-integration-current-cli/logs/aarch64-apple-darwin/stage4-native-build.log`
- Stage 3 does not expose `check`; the one direct probe returned
  `error: unknown command 'check'`.

## Failure boundary

The source is an ordinary `while` plus `if`/`elif` option parser. At source
line 63 the Stage 4 log reports `unexpected token ... 'elif'`, but adjacent
`parser_error_ctx` rows contain unrelated/corrupted token text such as
`receive`, `receive:`, `async`, `loop`, `importasreturn`, and
`andorval`. Later errors reinterpret `false`, colons, `else`, and `return`.
The failure therefore is not evidence that the source grammar is invalid; it
shows that the self-hosted multi-file lexer/parser is reading stale or
cross-file token/source state.

Commit `01b5080f00` (`preserve lexer source across files`) is present in the
failing Stage 3 source, so that repair is incomplete for the Stage 4 in-process
multi-file path.

## Required root fix

Add a same-process parser regression that parses at least two files whose
identifiers deliberately contain the misleading words above, then parses
`log_modes.spl` and proves every token text/span belongs to the current source.
Trace the `CoreLexer` slot and parser arena/source owner across
`phase2:parse:file:start` and `phase2:parse:file:done`; reset or replace the
owner at the file boundary without retaining pointers into the prior source.

The regression must run through the real Stage 3-driven Stage 4 multi-file
path. A single-file seed parse, source rewrite, reserved-word rename, or
special case for `log_modes.spl` is not an accepted fix.

## Session guard

Do not rerun the same full bootstrap in this session. The first result already
localizes the current exact-source gate, and the WM host/QEMU evidence remains
blocked until a test-capable exact-current CLI can be produced.

## 2026-07-31 pure-Simple care pass

The current pure-Simple Stage 3 at `c0d1ed…` no longer reproduces the original
`log_modes.spl` lowering failure. A focused native build of
`cli_log_modes_spec` completed four objects. A separate minimal program called
`parse_log_options`, printed the expected post-parse values, and exited 0.
Those results clear `log_modes` compilation and the minimal parser path only.

Starting the standalone SSpec binary directly produced a nil-receiver runtime
error and `SIGILL`. Because that invocation bypassed the canonical runner, it
is invalid evidence and does not establish an SSpec result.

Three bounded full-CLI cycles then established a later blocker:

1. two workers timed out at 600 seconds with zero completed reusable objects;
2. eight workers hit the 1.5 GiB cap and exited 134 with zero completed
   reusable objects; and
3. four workers reached linking after 1,500 objects, then failed because the
   selected core-C runtime bundle did not provide required symbols (including
   `parse_cmm_source`, `rt_stdin_read_line`, `rt_http_request`, and platform
   renderer symbols).

The exact retained full-CLI logs are under the isolated
`simple-browser-go-wt` worktree:

- `build/native_probe/interpret-dispatch-care/logs/baseline-build.log`;
- `build/native_probe/interpret-dispatch-care/logs/baseline-build-cycle2.log`;
  and
- `build/native_probe/interpret-dispatch-care/logs/baseline-build-cycle3.log`.

Focused evidence is separately retained at
`build/native_probe/log-modes-care/logs/cycle-1.log`,
`min-build-cycle-1.log`, `min-run-cycle-1.log`, and `run-cycle-1.log` in that
same worktree.

Candidate `3f3e0bd59963766e320289d96803ab1d3dcae44b` remains rejected and
unpushed. This care pass made no compiler edit, full bootstrap, deployment, or
runtime/SPipe PASS claim. The next action is to fix runtime-bundle authority as
a separate lane, then run a behavioral phase-trace SSpec using the exact steps
`Compile the runner fixture`, `Enter interpreter mode after checks`, `Skip
native monomorphization`, and `Run the requested SSpec`.
