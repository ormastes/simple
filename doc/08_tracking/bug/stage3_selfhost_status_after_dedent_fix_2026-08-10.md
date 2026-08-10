# Stage-3 self-host status after `ee89798a19f` (parse_module_body Dedent absorb)

- **ID:** stage3_selfhost_status_after_dedent_fix_2026-08-10
- **Status:** IN PROGRESS — no `^error:` observed; recorded so the next stream resumes instead of restarting
- **Why this file exists:** the two prior streams on this question both died
  mid-verification without reporting an after-state. This records the exact
  reproduction command and the observed progress point.

## Reproduction (does NOT touch `bin/` or `bin/release/**`)

Replays the recorded stage3 invocation from
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
using the already-admitted stage2 binary, writing the candidate to scratch:

```sh
P=$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu
OUT=<scratch>            # NOT bin/, NOT bin/release/
env -i HOME=$OUT/home TMPDIR=$OUT/tmp LC_ALL=C LANG=C \
  PATH=/usr/lib/llvm-18/bin:/usr/local/bin:/usr/bin:/bin \
  RUST_LOG=error LIBRARY_PATH= \
  SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NATIVE_ARENA_DECLS=1 SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_TIMEOUT_SECONDS=3600 \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_BUILD_TARGET=x86_64-unknown-linux-gnu \
  SIMPLE_NATIVE_BUILD_THREADS=4 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR=$OUT/cache \
  SIMPLE_RUNTIME_PATH=$P/stage2-runtime-authority \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
  SIMPLE_BINARY=$P/stage2-admitted/simple \
  $P/stage2-admitted/simple native-build \
    --target x86_64-unknown-linux-gnu --backend llvm \
    --runtime-bundle core-c-bootstrap --threads 4 \
    --cache-dir $OUT/cache --mode dynload \
    --runtime-path $P/stage2-runtime-authority \
    -o $OUT/stage3_simple src/app/cli/bootstrap_main.spl
```

Filter the log with `/usr/bin/grep -a -E "^error"` — it is otherwise unreadable.
Report the FIRST such line, not the last.

`SIMPLE_BOOTSTRAP=1` is carried because the recorded transcript sets it, but be
aware it MASKS real failures as a bare `rc=1`; never accept `rc=1` with no
`^error:` line as a diagnosis.

## Observed so far

- **29 minutes elapsed, process alive, zero `^error:` lines.**
- Progress point: past the frontend, into HIR lowering. The only log output is
  the field-type probe:
  `[hir-field-type] struct=CompiledUnit field=entry_point …` and
  `[hir-field-type] struct=BackendError field=span …`.
- No candidate binary at `$OUT/stage3_simple` yet.

## The two previously documented blockers

1. **`unresolved type: ByteOrder` in `cache_validator.spl` — appears addressed.**
   `src/compiler/80.driver/cache/cache_validator.spl:38` now carries an explicit
   `use std.binary_io.{ByteOrder}`, with a comment at lines 28-30 explaining it
   exists because the body of `shb_read_header` resolves `ByteOrder.LittleEndian`
   and `shb_reader.spl`'s own import does not carry across. Not re-triggered in
   this run.

2. **`Effect` facade collision — material still present, has not fired yet.**
   Six co-compiled declarations in owned source:
   `src/compiler/00.common/effects_phase3a.spl:1` (enum),
   `src/compiler/50.mir/mir_effects.spl:62` (enum),
   `src/compiler/20.hir/hir_types.spl:959` (**struct**),
   `src/compiler/30.types/type_system/effects.spl:18` (enum),
   `src/lib/common/ui/effect.spl:11` (enum),
   `src/lib/nogc_async_mut/effects.spl:17` (enum).
   The struct-vs-enum split at `hir_types.spl:959` is the most likely collision
   source. Check this first if the run ends on an `Effect` diagnostic.

## Next step for whoever picks this up

Re-run the command above and read the first `^error:`. If it completes, the
candidate is at `$OUT/stage3_simple` — **report its path, do not relink
`bin/simple` and do not write under `bin/release/**`.**
