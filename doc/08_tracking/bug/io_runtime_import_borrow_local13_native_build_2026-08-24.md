# Importing `std.nogc_sync_mut.io_runtime` fails native-build on a borrow-checker error

**Status:** Open — blocker for every `native-build` of a module importing `io_runtime`
**Observed:** 2026-08-24
**Area:** borrow checker / HIR import dependency resolution

## Relationship to the `unsafe` defect (read this first)

Split out of `unsafe_expression_import_lowering_2026-08-24.md`. That record
claimed "**every** `native-build` on `origin/main` is blocked" by the lexical
`unsafe` defect, using an `io_runtime`-importing control fixture as evidence.
That attribution was wrong on two counts:

- The `unsafe` defect was a **stale seed binary**, and is resolved. See the
  retraction section of that record.
- The control fixture still fails with a freshly built seed, but on **this**
  defect, which has nothing to do with `unsafe`. All three `unsafe`-defect
  signatures now count zero on this fixture: `function 'unsafe' not found` = 0,
  `unresolved identifier 'ffi'` = 0, `env_get ... body compilation failed` = 0.

So this — not `unsafe` — is what currently blocks `io_runtime` importers.
Standalone native-builds that do not import `io_runtime` succeed.

## Reproduction

Seed: `cargo build --release --bin simple` at `origin/main` (BUILD_RC=0),
binary size 60513440, mtime 2026-08-24 18:12. No source modifications.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ "$SEED" native-build control.spl -o control.bin
$ NB_RC=$?      # read directly, not through a pipe
NB_RC=1
```

## Verbatim errors

```text
error: 37:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 43:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 54:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 66:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
error: 73:1: borrow of `local(13)` may still be active at return|||RELATED:6:1:borrow created here|||HELP:ensure borrow ends before returning
```

Accompanied by unresolved import-dependency origins, which may be the same root
cause or a second defect — unseparated as yet:

```text
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime dependency=Option: no declaration, re-export hop, or explicit import of this name in the owner; a later `unresolved type: Option` will be reported against an importing module instead
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime dependency=Result: no declaration, re-export hop, or explicit import of this name in the owner; a later `unresolved type: Result` will be reported against an importing module instead
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops   dependency=Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops   dependency=Option: ...
```

Note the diagnostic's own wording: the unresolved origin is deliberately
deferred and "reported against an importing module instead", which is why the
failure surfaces in the trivial caller rather than in `io_runtime` itself.

## Required next evidence

- Determine whether the `borrow of local(13)` errors and the unresolved
  `Option`/`Result` dependency origins share a root cause, or are two defects.
- Identify which `io_runtime` declarations the line numbers (37, 43, 54, 66, 73)
  refer to — they are reported without a file path, which is itself a
  diagnostic-quality gap worth fixing.
- A regression gate should be behavioural (native-build a fixture importing
  `io_runtime` and require NB_RC=0), following the pattern of
  `scripts/check/check-unsafe-block-native-build.shs`.

## Not this defect

Lexical `unsafe` in either form. Both the statement/block and the
expression/value form native-build and execute correctly, pinned by
`scripts/check/check-unsafe-block-native-build.shs` (`PASS — 3 case(s) checked`).
