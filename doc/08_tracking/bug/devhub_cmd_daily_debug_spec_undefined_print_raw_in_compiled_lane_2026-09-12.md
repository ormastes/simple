# devhub cmd_daily_debug_spec loses its whole file in the compiled lane: `undefined identifier: print_raw`

- Status: OPEN (2026-09-12)
- Area: app / devhub (spec harness), compiler / SMF lowering
- Severity: medium (a 25-case unit spec is reduced to one synthetic failure in every
  directory run, and the loss is silent in single-file runs)
- Found by: TODOFIX-0 lane while implementing todos 44/45. Proven PRE-EXISTING (A/B below);
  not fixed here, out of shard scope.

## Symptom

Single-file (interpreter lane) the spec is green:

```
bin/simple test test/01_unit/app/devhub/cmd_daily_debug_spec.spl
SPEC FILE VERDICT: ... outcome=OK declared>=25 executed=25 passed=25 failed=0
```

In a whole-DIRECTORY run, which compiles each spec to standalone SMF, the file does not
lose a case — it fails to compile and collapses:

```
bin/simple test test/01_unit/app/devhub/
FAIL test/01_unit/app/devhub/cmd_daily_debug_spec.spl (0 passed, 1 failed)
error: compile failed (..._cmd_daily_debug_spec_spec_native.spl): semantic:
  Undefined("undefined identifier: print_raw")
SPEC FILE VERDICT: ... outcome=ERROR declared>=1 executed=1 passed=0 failed=1
(whole dir: 502 total, 475 passed, 27 failed, 12 skipped)
```

`print_raw` appears nowhere under `src/app/devhub/**`; it is defined in
`src/lib/nogc_sync_mut/sffi/diag.spl:45`, `src/runtime/simple_core/core_string.spl:1465`
and declared `extern` in three mcp modules, so the compiled lane is resolving it from a
module the interpreter reaches but the SMF path does not.

## Why the sibling passes

`test/01_unit/app/itf/cmd_daily_debug_spec.spl` — a near-clone — ALSO fails to compile,
but with `cannot compile to standalone SMF: 85 function(s) contain constructs that require
the interpreter`. That diagnostic makes the runner DEGRADE to the interpreter, and the file
passes 21/21. A hard `Undefined(...)` gets no such fallback. The fallback path is therefore
the thing that differs, not the spec.

## A/B: this is pre-existing, not caused by the 2026-09-12 date-stamp change

Commit `915d2f86261` added six cases to this spec and a `std.common.time_utils` import to
`src/app/devhub/cmd_daily_debug.spl`. Restoring the spec as it was at `915d2f86261~1` into
a two-spec temp directory (with a known-good neighbour) and running that directory:

```
SPEC FILE VERDICT: .../zz_probe_devhub/text_diff_spec.spl       outcome=OK    executed=8 passed=8 failed=0
SPEC FILE VERDICT: .../zz_probe_devhub/cmd_daily_debug_spec.spl outcome=ERROR executed=1 passed=0 failed=1
  -> Undefined("undefined identifier: print_raw")
```

The PRE-change spec fails identically. Independently: the only import that change added,
`std.common.time_utils`, has **zero** `use` statements of its own — it is a leaf module of
pure arithmetic plus externs — so it cannot pull `print_raw` into the module graph.

Binary: Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 prefix `3d120a6f`.

## Fix direction (not attempted here)

Either resolve `print_raw` on the SMF path the way the interpreter does, or make an
unresolved identifier in a wrapped spec degrade to the interpreter like the
"requires the interpreter" diagnostic already does, so a spec is never silently reduced
to one synthetic failure.
