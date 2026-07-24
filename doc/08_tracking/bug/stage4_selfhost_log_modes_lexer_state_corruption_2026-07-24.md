# Stage 4 self-host corrupts lexer state at `log_modes.spl`

- **Status:** resolved by Cranelift literal rodata ownership fix; later Stage 4 source error remains separate
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

## Resolution evidence — 2026-07-25

The corrupted tokens were caused below the lexer: Cranelift lowered bytes passed
to `rt_string_new_literal` into reusable stack slots even though the runtime
interns that API by stable `(address, length)`. Equal-length literals from
different functions therefore collided when their stack addresses were reused.
Commit `2acc9c729c` changes
`src/compiler_rust/compiler/src/codegen/instr/helpers.rs` to declare immutable
module data and use `declare_data_in_func`/`global_value`.

One exact isolated rebuild with `SIMPLE_NO_STUB_FALLBACK=1` produced:

- Stage 2 SHA-256:
  `77bae657a38c9e11b759c0699720a4970b71aefe0838529daa78240346bd75bf`
- Stage 3 SHA-256:
  `6fb5fd8260aee111b6325ccba1e6669a3f09061368511e3ec4f0dd352d3c74ce`
- Preserved pre-fix log:
  `build/wm-integration-current-cli/logs/aarch64-apple-darwin/stage4-native-build.pre-rodata-fix.log`
- Current build log:
  `build/wm-integration-current-cli/final-rodata-bootstrap.log`

The current Stage 4 parsed `log_modes.spl` successfully, then parsed more than
thirty subsequent CLI modules without corrupted diagnostic fragments. It
stopped at a real source error in
`src/app/io/_CliCompile/compile_targets.spl:1397`: a boolean expression was
continued at a deeper indentation without parentheses. That source now uses
the repository's established parenthesized continuation form. The full build
was not repeated because this was the one retained Stage 4 attempt for the
session.
