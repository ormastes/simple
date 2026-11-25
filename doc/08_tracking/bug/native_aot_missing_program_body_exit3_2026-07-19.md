# `compile --native` binary omits program body — silent exit 3 (NIL sentinel)
## Closed 2026-09-16 — ...e callee name built on the stack. ## FIX APPLIED (fail loudly; seed pipeline/execution.rs,

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Filed:** 2026-07-19 · **Status:** SOURCE FIXED; native execution pending · **Area:** native AOT / linker
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

## ROOT CAUSE (2026-07-19, verified source-level + disassembly)
NOT dead_strip / reachability / Engine2D / arg-count (all disproved by a
20-rung bisection in build/tmp/aotbody/). Mechanism:
`compile --native` (driver/src/cli/compile.rs:687 →
pipeline/execution.rs:882→911) runs `compilability::analyze_module`
(compiler/src/compilability.rs) — the HYBRID-JIT classifier — and any
function containing a flagged construct (`Expr::FString` string
interpolation, compilability.rs:535-556, is the common one; ~19 others:
closures, pattern match, generators, async, try, actor ops) is marked
"requires interpreter". execution.rs:1013-1019 then applies
`mir::apply_hybrid_transform` (mir/hybrid.rs:39,49), rewriting every call
to it into `MirInst::InterpCall` → codegen (codegen/instr/core.rs:758)
emits `rt_interp_call(name, argc, args)`. In a standalone native binary no
interpreter handler is ever registered, and the bridge
(runtime/src/value/sffi/interpreter_bridge.rs:32-39) **unconditionally
returns NIL** → silent no-op call, exit 3, body never emitted (hence
22-symbol 58KB binaries). Disassembly confirms `_spl_main` branches to
`_rt_interp_call` with the callee name built on the stack.

## FIX APPLIED (fail loudly; seed pipeline/execution.rs, cargo-check green)
`compile --native` now hard-errors (UNSUPPORTED_FEATURE) listing every
interpreter-required function with its FallbackReasons instead of emitting
a silently-nil binary. Escape hatches: `SIMPLE_NATIVE_ALLOW_INTERP_CALLS=1`
or bootstrap mode → loud warning + old behavior. Hybrid `run` lane
untouched. Takes effect on next seed rebuild. Follow-up (open): narrow the
FString classifier for the AOT path — native interpolation codegen already
works, so interpolation should not force interpreter routing.

Side finding: files with no qualifying global-init import fail to link with
undefined `___module_init` — separate pre-existing defect.

## Original hypothesis (superseded)
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


## Re-verification 2026-11-25 (release/1.0.0, work/p2w3-ac-20261125) — fix confirmed in source; native execution blocked by unrelated Windows linker defect

Source inspection at release/1.0.0 confirms both halves of the resolution are
present:

1. **Fail-loud fix:** `src/compiler_rust/compiler/src/pipeline/execution.rs:1170-1219`
   hard-errors with `UNSUPPORTED_FEATURE`, listing every interpreter-required
   function with its `FallbackReasons`, unless `SIMPLE_NATIVE_ALLOW_INTERP_CALLS=1`
   or bootstrap mode — exactly the fix this doc records. The comment at :1175
   cites this doc.
2. **The follow-up FString narrowing also landed:**
   `src/compiler_rust/compiler/src/compilability.rs:81-85,767+` — FString
   constructs proven to lower to native calls (`MirInst::FStringFormat` in
   `codegen/llvm/functions.rs`) no longer force interpreter routing, so plain
   string interpolation no longer trips the classifier.

Execution limit, stated plainly: a native-compile smoke on this Windows host
(`bin/simple.exe compile --native` on a 5-line interpolation repro) could not
reach the link step — the seed driver passes Unix-style `-o <path>` to
`lld-link`, which ignores it and then fails with
`lld-link: error: could not open '<output>': No such file or directory`.
That is a separate, unrelated Windows-lane driver/linker-argument defect in
the Rust seed (not this bug, not fixed here per the no-Rust-builds rule). The
interp-call fail-loud path itself was therefore verified by code inspection
only. Status: CLOSED (unchanged).
