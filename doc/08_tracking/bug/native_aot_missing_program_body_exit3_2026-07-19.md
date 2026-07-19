# `compile --native` binary omits program body — silent exit 3 (NIL sentinel)

**Filed:** 2026-07-19 · **Status:** OPEN · **Area:** native AOT / linker
**Blocks:** running showcases as native binaries (the fast lane that escapes
the interpreter wall now that the LINK step is fixed).

## Symptom
`bin/simple compile --native examples/06_io/ui/graphics_2d_showcase.spl`
(with `SIMPLE_LINKER=ld SIMPLE_RUNTIME_PATH=$PWD/build/simple-core`, see the
link-fix recipe in showcase_lanes_regressions_2026-07-18.md item 7) links a
valid ad-hoc-signed Mach-O that runs without crashing but prints NOTHING and
exits with code **3** — none of the app's internal prints fire.

## Evidence
- The 2D showcase's AOT SMF artifact is ~14MB, but the linked native binary
  is **58,952 bytes** — and a 6-line hello-style repro compiles to 59,008
  bytes. The binary size is invariant of program size: the emitted native
  code contains the shim plus at most a sliver of the program, not the app.
- Exit code 3 == the runtime NIL sentinel (`NIL_VALUE=0x3`, see project
  memory on spl_dlopen): `main()`'s call into the missing
  `run_graphics_2d_showcase` body evaluates to nil → 3.
- Interpreter oracle on the same file: full render + stats, exit 0.
- Reproduces at `--opt-level none` and `aggressive` (not a dead-strip
  artifact of optimization level).
- NOT a scalar-argument-call bug: a minimal module importing Engine2D with
  `fn f(x: bool) -> i64: print "in f"; 42` called from main compiles native
  and runs CORRECTLY (in f / 42 / exit 0) when compiled from `build/tmp/`.
  (An earlier agent reduction claiming any 1-scalar-arg call fails was
  confounded — likely by compiling repros inside `examples/06_io/ui/` where
  sibling-import resolution differs.)

## Hypothesis (unverified)
Native codegen's reachability/emission drops function bodies beyond some
boundary (imported-module bodies? functions above a size threshold?) — nm
confirms: the g2d binary has only ~22 T symbols and NO
`run_graphics_2d_showcase`/`draw_showcase` symbols at all (the 6-line repro
binary has 26 T symbols, nearly the same set = shim+runtime only) — and
calls to non-emitted functions resolve to a weak nil-returning stub instead
of failing the link. `-dead_strip` in the ld64 line may also remove bodies
that lost their references. Next probe: `nm build/tmp/aot_repro_bin` vs the
g2d binary — count emitted `_spl`/module symbols; then bisect at module
boundary (call a fn defined in an imported module vs same-module).

## Repro
```
SIMPLE_RUNTIME_PATH="$PWD/build/simple-core" SIMPLE_LINKER=ld \
  bin/simple compile --native examples/06_io/ui/graphics_2d_showcase.spl -o /tmp/g2d
SHOWCASE_RESOLUTION=320x240 /tmp/g2d ; echo $?   # -> silent, 3
```
