# Self-hosted CLI native-build silently returns success without an artifact

Status: **OPEN / restart12 render lane blocker**

Owner: pure-Simple CLI/native-build dispatch —
`src/app/cli/_CliMain/main_and_help.spl`,
`src/app/io/_CliCommands/run_commands.spl`,
`src/app/io/_CliCompile/compile_targets.spl`, and
`src/app/cli/native_build_main.spl`.

Unblock condition: construct and provenance-admit a source-matched Stage 4 CLI,
prove a minimal cached one-binary entry closure plus the negative missing-output
gate, deploy it with a hash/rollback receipt, then build and execute the sparse
DrawIR carrier described in
`doc/07_guide/ui/rendering/cached_render_entry_closure.md`.

The unadmitted artifact at `release/x86_64-unknown-linux-gnu/simple` cannot
currently produce the cached native entry closure required by the sparse DrawIR
8K benchmark. Canonical deployment/provenance receipts are absent, so this file
does not classify it as a deployed pure-Simple CLI.

On 2026-08-14 three bounded command variants were attempted. The first used the canonical
entry-closure command before its output directory existed. The second created
that directory and changed the output name. The third selected
`--backend=llvm`, `--verbose`, and another fresh output name. Every invocation
exited 0 in about 1.4 seconds, printed nothing, and produced no output file.
These are diagnostics, not three implementation fix cycles.

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

This is consistent with, but does not prove, a stale or miscompiled dispatcher
or entry closure in the artifact. It blocks producing the render benchmark
carrier. The next lane must first admit and deploy a source-matched CLI that
proves a minimal native-build artifact and the missing-artifact negative gate;
only then should it build and run
`test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl`.

No 8K performance conclusion can be drawn from these failures.

Deterministic resume sequence: use the six gates in the canonical plan at
`doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`; retain
candidate/provenance, essential-smoke, deploy, minimal-carrier, negative-gate,
benchmark, `/usr/bin/time`, and checksum/readback receipts under
`build/bootstrap/` and `build/restart12-render/` as named by those gates.
