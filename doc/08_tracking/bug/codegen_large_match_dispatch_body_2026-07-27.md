# Codegen fails on very large function body: _dispatch_function (236-arm match, 2497 lines)

- **Date:** 2026-07-27
- **Lane:** stage4 native-build (cranelift), full-CLI closure
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Symptom
`native-build` of `src/app/office/sheets/formula.spl` fails:
```
codegen: Module error: 1 function body/bodies failed to compile: [_dispatch_function];
set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe)
```
`_dispatch_function` (formula.spl:4270-6767) is a single 2497-line function whose
body is one `match canonical_name:` with **236 quoted string arms** (Excel
function dispatch). It also first hit a 300s per-file compile TIMEOUT before the
codegen error surfaced (raised to 900s to get past the timeout).

## Assessment
Per project rule "Compiler auto-optimizes patterns — don't make users rewrite for
perf; fix it in the compiler": a 236-arm match SHOULD compile. This is a codegen
scalability limit on large function bodies / large string-match lowering, not a
user error. Regression window: grew with `15b03323ee feat(office): add full-size
Calc TUI UI access`.

## Two fixes
1. **Proper (compiler):** make codegen handle large match/function bodies (chunked
   lowering, or lower a big string-match to a table/hash dispatch instead of a
   linear IR chain). Codex/compiler territory.
2. **Workaround (source, to unblock deploy):** split `_dispatch_function` into
   category sub-dispatchers (math / stats / text / lookup / logical …), each a
   separate `fn` with a manageable arm count, called in sequence. Preserves exact
   behavior; gets each body under the codegen limit. Being applied to unblock the
   stage4 deploy while the compiler fix is pending.

## App-side symptom re-verification 2026-08-17 (app-lane worker) — STILL OPEN, NOT OWNED HERE

App-side shape unchanged in current source:

- `src/app/office/sheets/formula.spl` is **9846 lines**.
- `_dispatch_function` is still the single dispatch chokepoint, called from
  `formula.spl:134` (`val probe = _dispatch_function(upper, [[1.0, 2.0]], sheet)`)
  and `formula.spl:3407` (`val result_val = _dispatch_function(name, args, sheet)`),
  and documented as such at `formula.spl:2721`.

The defect itself is a **codegen** defect (cranelift function-body compilation),
whose fix belongs in `src/compiler/50.mir/**` or `src/compiler/70.backend/**` —
owned by a different lane. This worker deliberately made **no** compiler edit and
**no** app-side split of `_dispatch_function`: splitting the match to dodge a
codegen limit would hide the compiler defect behind a workaround, which the
project rules forbid. Not re-executed: a `native-build` of formula.spl was not
attempted, because an unrelated `native-build` on this host exceeded 300s wall
under the concurrent bootstrap load (rc=124) and would not have been evidence.
