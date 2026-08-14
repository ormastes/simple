# Self-hosted CLI native-build silently returns success without an artifact

Status: **OPEN / restart12 render lane blocker**

The deployed pure-Simple CLI at
`release/x86_64-unknown-linux-gnu/simple` cannot currently produce the cached
native entry closure required by the sparse DrawIR 8K benchmark.

On 2026-08-14 three bounded attempts were made. The first used the canonical
entry-closure command before its output directory existed. The second created
that directory and changed the output name. The third selected
`--backend=llvm`, `--verbose`, and another fresh output name. Every invocation
exited 0 in about 1.4 seconds, printed nothing, and produced no output file.

Direct source execution is independently broken: both `-c 'print(123)'` and
the canonical benchmark path exit 248 with `missing command` before compiler or
renderer receipts. `SIMPLE_NO_BOOTSTRAP_DELEGATE=1` does not change that
result. The artifact has no colocated `simple_seed`, so this is not accepted as
bootstrap delegation evidence.

Current source already contains two fail-closed checks that the deployed
artifact does not exhibit:

- `src/app/io/_CliCompile/compile_targets.spl` rejects driver Success when its
  staged output is absent.
- `src/app/cli/native_build_main.spl` rejects a worker exit 0 when the requested
  output is absent.

This indicates a stale or miscompiled dispatcher/entry closure in the deployed
CLI. It blocks rebuilding that same CLI and blocks producing the render
benchmark carrier. The next lane must first deploy a source-matched CLI that
proves a minimal native-build artifact and the missing-artifact negative gate;
only then should it build and run
`test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl`.

No 8K performance conclusion can be drawn from these failures.
