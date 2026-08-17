# native-build cannot resolve a class static method with trailing default params

**Status:** OPEN (P1 — this is what blocks every push)
**Filed:** 2026-08-17
**Component:** native-build MIR lowering, class/static-method resolution
**Class:** engine divergence — the seed resolves it, native-build does not

## Symptom

`sh scripts/check/check-native-trailing-default-param.shs` is RED, so the
pre-push hook blocks every push. Measured directly against the fixture, exit
code read into a variable on the line AFTER the command, never through a pipe:

```
bin/release/x86_64-unknown-linux-gnu/simple native-build \
    test/fixtures/native_trailing_default_param/main.spl -o /tmp/ntdp_mine.bin
BUILD_RC=1
```

```
[ERROR] MIR error: MIR lowering error: undefined variable Widget
[ERROR] MIR error: MIR lowering error: unresolved method call: stat
error: build failed: 1 failed, 0 unverified, 0 not run, 1 ok of 2 unit(s)
       — ERROR: test.fixtures.native_trailing_default_param.main
```

The fixture is small and the two named symbols are both in it:

```
27: class Widget:
34:     static fn stat(a: i64, b: i64 = 55, c: bool = false) -> i64:
52:     var w = Widget(base: 100)
56:     Widget.stat(2)
```

So native-build fails to resolve both the constructor call `Widget(base: 100)`
and the static call `Widget.stat(2)`. This is a **MIR lowering** failure, not a
parse failure — the file parses.

## Correction to an earlier attribution

This blocker was previously described, in session notes and in a subagent brief,
as a **parser** defect at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:49` — a module-level
`var mir_lower_parent_expr_file: text = ""` that the pure-Simple parser
supposedly rejects. **That is wrong and should not be carried forward.**

- Every `expr_dispatch.spl` entry in the build log is a **warning**, not an
  error: two `export use *` advisories and two deprecated bracket-generics at
  `expr_dispatch.spl:3074` / `:4056` (`field_reprs[field_idx]`).
- Line 49 does not appear in the log at all.
- A bug row `native_build_parser_rejects_module_level_var_init_2026-08-17.md`
  was believed to exist for it. **No such file is in the tree.**

The attribution was propagated from a stale brief without being re-derived
against a build log, and a subagent was dispatched on it. It ran out of session
budget before spending it on the wrong file.

## Evidence hazard found while reproducing this

native-build **truncates its own worker stderr from the middle**:

```
!!!!!! NATIVE-BUILD STDERR TRUNCATED !!!!!!
[native-build] TRUNCATED: 55780 of 67780 bytes of worker stderr were dropped
               from the MIDDLE.
[native-build] Raw head+tail below is INCOMPLETE -- counting over it is unreliable.
```

82% of the diagnostics are dropped, and the two `MIR lowering error` lines above
are among the casualties — they survive in one run's log and are absent from the
next. Anyone re-running this and grepping for the error may find nothing and
conclude the defect is gone. It is not; the evidence was discarded.

Separately, the guard itself wrote to a fixed `/tmp/...last.log`, which a
concurrent run truncated to 0 bytes mid-read. Fixed in the same change (the path
is now PID-unique).

## Fix direction

Find where native-build's MIR lowering resolves class constructors and static
methods, and make a `static fn` with trailing default parameters resolvable from
a sibling call site. The guard exists precisely to pin this shape, and its
fixture asserts several call shapes — expect more than one to be affected.

## Not verified

- Whether the two errors share a root cause or are independent (a class-surface
  gap would explain both; that was not established).
- Whether non-static methods with trailing defaults resolve correctly.
- Whether the JIT lane shares the defect — only native-build and the seed were
  compared.
- The guard's real PASS path has never been observed, since the fixture has not
  compiled; PASS currently rests on a selftest stub only.
