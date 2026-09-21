# Codegen fails on very large function body: _dispatch_function (236-arm match, 2497 lines)

## Fixed 2026-09-21 — bounded formula dispatch

The current Formula leaf had 229 dispatch arms. HIR lowers non-integer literal
matches through `build_if_chain`, so the former single body became one deeply
nested conditional tree containing every arm body. The Phase 2 full CLI build
timed this file out at 600 seconds; the earlier focused profile retained more
than 3 GiB while converging the same leaf.

`formula.spl` now routes names into eight alphabetic helpers of at most 39
arms. All 229 names and the unknown-function behavior are preserved. The
focused functional regression is
`test/01_unit/app/office/sheets/formula_dispatch_partition_spec.spl` and the
cold compiler/RSS gate is
`test/05_perf/compiler/formula_dispatch_compile_resource_profile.shs`.

Measured with the admitted macOS Phase 2 compiler
`35acf59774028cb8849812abf5762330dfd16f232dacb9bb3b278f176e8b0669`:

- 30 compiled, 0 cached, 0 failed;
- 115.6 seconds compile, 18.2 seconds link, 134 seconds wall;
- 923,844,608 bytes maximum RSS; and
- `SIMPLE_NO_STUB_FALLBACK=1` with isolated frontend, HIR, and native caches.

The retained pre-fix Phase 2 evidence is
`build/evidence/phase2-test-20260921/run-2/work/logs/compiler_cli_build.log`
(`formula.spl: timeout (600s)`).

The functional SSpec is retained but could not be executed in this lane: the
canonical Phase 2 test-runner build is itself blocked by the other Phase 2
failure clusters, and the admitted compiler capsule intentionally exposes only
`compile` and `native-build`. No seed or release alias was substituted. The
native compile/resource gate above is executed evidence; run the SSpec with the
first admitted test-capable post-fix runner.

### SoSIX compatibility audit

This change adds no extern, SFFI, runtime, provider, loader, filesystem,
process, environment, ABI, or host-interface surface. It only partitions one
pure-Simple function inside the existing Office module and keeps the same
imports and public API. SoSIX compatibility is unchanged; no SoSIX-specific
provider or test update is required.

- **Date:** 2026-07-27
- **Lane:** stage4 native-build (cranelift), full-CLI closure
- **Status:** open — blocks stage4 full-CLI build (last remaining compile blocker)

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
