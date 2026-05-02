# Watchdog kill — rv64_boot_spec preceded by IN_IMMUTABLE debug-print storm — 2026-04-28

Cross-ref: `.sstack/fix-perf-bugs/timeout_triage.md` (kill #2, line 3169)
and `dsl_spec_wedge_2026-04-27.md` (runner-attribution bug).

## TL;DR

In the slow_run, the second watchdog kill (line 3169) was preceded by 14
consecutive `DEBUG FieldAccess: self.w assignment with IN_IMMUTABLE=true`
debug prints, attributed to `test/integration/os/rv64_boot_spec.spl`.

**The debug print is already removed** in the current source tree by commit
`493077d162` ("...fix..."). The line is gone from
`src/compiler_rust/compiler/src/interpreter/node_exec.rs` (now around L638)
— only the `cannot modify self.{field}` semantic error remains.

When run today on the current binary:

```
$ timeout 90 bin/simple test test/integration/os/rv64_boot_spec.spl
... 358ms ... 7 passed / 11 failed (semantic / array-index errors), no hang
```

The spec finishes in **<400 ms**. The "IN_IMMUTABLE debug-print storm"
hang is fixed for current source.

## Symptom (slow_run only — historical)

```
DEBUG FieldAccess: self.w assignment with IN_IMMUTABLE=true   x14
[watchdog] wall-clock timeout (60s) exceeded
```

The debug print fired on every assignment to `self.w` in an immutable-fn
method. For RISC-V boot tests that update register-file fields each cycle
this could storm stderr (linear in instruction count). The printing was
not strictly the cause of the hang — but `eprintln!` of N×100k lines is
slow enough to push past the 60 s budget on a long boot scenario.

## Root-cause class

**Debug-print storm** in the interpreter's
`E1052 cannot modify self in immutable fn method` check. Already fixed
upstream — debug-print removed.

The 11 remaining `expected true to equal <int>` / `cannot index array
with type 'bool'` failures in `rv64_boot_spec.spl` are **separate, real
test bugs** in the spec (or in the underlying `rv64regfile`/ALU module),
not interpreter pathologies.

## Reproduction

Pre-fix: not reproducible (debug print removed).

Today:

```bash
$ timeout 90 bin/simple test test/integration/os/rv64_boot_spec.spl
# Completes in ~358 ms, 11 functional failures, no hang.
```

## Proposed fix shape

1. **Hang-class fix: already landed.** Commit `493077d162` removed the
   `eprintln!("DEBUG FieldAccess: ...")` line. No further compiler fix
   needed for the storm.
2. **Functional failures (separate)**: 11 failing it-blocks in
   `test/integration/os/rv64_boot_spec.spl` — need investigation:
   - `cannot index array with type 'bool'` (×2): probably indexing
     register file with the result of an inequality comparison instead
     of an integer.
   - `expected true to equal <int>` (×8): likely missing
     `expect(actual).to_equal(expected)` argument order — the spec is
     passing comparison results to `to_equal` rather than the int value.
   - `array index out of bounds: 0 vs 0` (×1) in UART byte-by-byte test.

   These are spec/module bugs. Recommend a follow-up `bugfix` task on
   `rv64_boot_spec.spl` and `src/os/...rv64...` register-file ops.

## Workaround

None needed — current binary handles the spec in <400 ms.

## Status

- Hang aspect: **FIXED** (commit `493077d162`).
- Functional regressions in spec: **OPEN** — separate task, not part of
  watchdog triage.
