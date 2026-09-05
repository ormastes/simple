# native-build cannot resolve a class static method with trailing default params

**Status:** OPEN (P1). Re-run 2026-08-17: the fixture build still produces NO
verdict — it fails as infrastructure before MIR lowering, so this row is neither
confirmed nor cleared. One contributing cause was fixed in that pass (the
unconditional trace flood, below).

## Re-run 2026-08-17

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59537240 bytes,
mtime 2026-08-17 12:58:51.

```
$ (ulimit -v 12000000; timeout 1500 nice -n 19 bin/simple native-build \
      test/fixtures/native_trailing_default_param/main.spl -o <scratch>/ntdp.bin)
BUILD_RC=255
error: native-build worker timed out after 7200s before producing a binary.
$ grep -c 'undefined variable Widget' <scratch>/ntdp.log
0
```

The zero count is NOT a pass — MIR lowering was never reached, so there was
nothing to report.

### The actual blocker, isolated: an 8 GiB single allocation, misreported as a timeout

A second run with a 20 GB address-space cap and a 3000s budget reached the same
point and printed the real cause in the worker's own stderr:

```
memory allocation of 8589934592 bytes failed
timeout: the monitored command dumped core
!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
error: native-build worker timed out after 7200s before producing a binary.
```

The worker **aborts on a single 8 GiB allocation** while loading the compiler
graph and dumps core; the driver then reports a *7200s timeout* — inside a 3000s
wall budget, for a process that lived minutes. Two consequences:

1. Neither this row nor the owner-unresolved row can be verified at all until
   that allocation is fixed: every verification run dies before MIR lowering.
2. `worker timed out after 7200s` is a **misclassification of an abort/OOM**, and
   its remediation advice ("Raise --timeout, shrink --source") points the reader
   the wrong way. This is what made commit `88d1078f3ef` read the failure as a
   slow / RSS-ballooning worker.

Measured, both runs identically: worker stderr 36907 bytes,
`[mir-method-call]` trace lines 0, `undefined variable Widget` 0 — nothing from
MIR lowering in either.

### Also fixed in this pass: the unconditional trace flood

Honest scope note first: it did **not** change these two runs (both logs are
byte-identical in size and contain zero trace lines, because lowering was never
reached). It is fixed because it is a real hazard for any run that DOES reach
lowering.

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` carried **38
unconditional** `eprint("[mir-method-call] ...")` probes, several of them on the
per-method-call entry path (`start`, `result-types`, `receiver-type`,
`resolution-enter`, ...). Lowering the whole compiler tree therefore emits tens
of megabytes of stderr, which feeds the truncator that drops the real
diagnostics from the MIDDLE of the log.

All 38 are now gated on `SIMPLE_MIR_METHOD_CALL_TRACE=1` (default off) via a new
`mir_method_call_trace_enabled()` helper in the same file — kept rather than
deleted, per `doc/07_guide/infra/logging/log_retention_policy.md`, and matching
the existing `SIMPLE_MIR_LOG_CONV` / `SIMPLE_MIR_FIELD_TRACE` pattern in this
layer. Verified mechanical: `diff` of the file before/after shows changes on the
trace lines and the new helper only.

This does not by itself resolve the resolution defect; it removes the evidence
hazard that has been masking it.
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
