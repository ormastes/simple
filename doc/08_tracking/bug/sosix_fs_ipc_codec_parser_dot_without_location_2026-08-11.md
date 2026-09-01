# SOSIX FS IPC codec parser dot diagnostic lacks a source location

**Status:** Claimed by the SOSIX parallel-QEMU integration lane

**2026-08-11 bounded triage:** Reproduced in the installed Rust bootstrap seed;
not reproduced by the seed's `check` frontend before its 30-second bound.  The
bug is not currently eligible to close as a concurrent fix.

## Exact reproducer

Checking or importing `src/os/sosix/fs/ipc_codec_v1.spl` stops before the
focused SOSIX specifications execute with:

```text
Unexpected token: expected LParen, found Dot
```

The diagnostic identifies the module but supplies no line or column. Direct
source checking can spend the repository CPU budget without improving the
location. The two `not helper(value.field)` expressions were mechanically
isolated and ruled out; those speculative edits were reverted.

## Required resolution evidence

1. Capture a parser-facing token/location result that identifies the exact
   construct; do not rewrite otherwise-valid codec semantics as a workaround.
2. Retain the exact codec reproducer and add one adjacent parser regression.
3. Execute the codec and positioned-dispatch focused specifications with an
   admitted pure-Simple compiler after bootstrap deployment.

The bug remains open until both parser evidence and focused execution pass.

## Bounded parser-probe evidence (2026-08-11)

Only three compiler probes were used:

1. `SIMPLE_COMPILER_TRACE=1 bin/simple check
   src/os/sosix/fs/ipc_codec_v1.spl` entered dependency analysis and emitted
   semantic/import warnings, with no dot parse diagnostic before the 30-second
   timeout.
2. `bin/simple compile src/os/sosix/fs/ipc_codec_v1.spl
   --emit-ast=/tmp/ipc_codec_v1.ast` reproduced in under one second:
   `parse: ... Unexpected token: expected LParen, found Dot`.  No AST was
   emitted and the seed diagnostic still omitted the token span.
3. An isolated adjacent shape containing `for byte in completion.payload:`
   compiled and emitted an AST successfully.  That field-access iterable is
   therefore ruled out as the triggering construct.

`bin/simple` resolved to `bin/release/x86_64-unknown-linux-gnu/simple` and
identified itself as a Rust bootstrap seed.  No admitted pure-Simple compiler
was present at the canonical path, so the required deployed-compiler evidence
could not be obtained.  The codec source is currently untracked by Git and had
a filesystem modification time of 08:46 UTC, before this bug record's 09:12
UTC modification time; there is no committed before/after revision from which
to infer a concurrent parser fix.

Do not add a semantic workaround or claim a parser regression from these
results.  The remaining next step is a location-preserving lexer/parser run
with an admitted pure-Simple compiler (or a seed rebuilt with the current
parser's span-bearing diagnostic).  Add the adjacent regression only after
that run identifies the precise source construct.
