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

## 2026-08-17 triage (wave W3) — FAMILY: no source-matched self-hosted binary deployed

This row is one member of a single family, not an independent defect. On this
host `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` is the **Rust
seed**, so every remaining blocker in this row requires building and deploying a
source-matched self-hosted CLI. The rows sharing that blocker are:

- `host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17`
- `stage4_full_cli_source_check_blank_exit8_2026-07-23`
- `self_hosted_cli_native_build_silent_no_artifact_2026-08-14`
- `self_hosted_simpleos_target_native_build_crash_2026-07-11`
- `native_selfhosted_run_segfault_startup_normalize_2026-07-24`
- `bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17`
- `mcp_full_program_native_codegen_and_arg_extract_2026-06-16`
- `no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09` (the family
  statement itself: an ENVIRONMENT fact on this machine, not a code defect)

W3 was explicitly barred from rebuilding or redeploying `bin/simple` /
`bin/release/**` (~16 concurrent lanes share them), so **no execution evidence
for this row was produced or is claimed**. Status is unchanged: OPEN, blocked on
deploy. What W3 did instead was pin, by source spec, the fail-closed checks these
rows depend on, so they cannot be silently lost again while the deploy blocker
persists: `test/01_unit/app/cli/silent_success_fail_closed_source_spec.spl`
(native-build worker exit 0 without an artifact; driver Success without a fresh
staged artifact; argv read through `rt_cli_get_args` rather than a same-named
import). Ablation-verified: neutralising the native_build_main.spl guard takes
that spec from `Results: 3 total, 3 passed` to `3 total, 2 passed, 1 failed`.

