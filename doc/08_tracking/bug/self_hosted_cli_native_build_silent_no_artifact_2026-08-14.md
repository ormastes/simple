# Self-hosted CLI native-build silently returns success without an artifact

Status: **RETIRED 2026-08-17 — the silent-no-artifact symptom does NOT reproduce.**
The residual render-lane blocker is a DEPLOY question, not this defect; see the
re-triage immediately below before reading the 2026-08-14 text, which is kept
verbatim for history but is superseded.

## 2026-08-17 re-triage (triage shard) — DID NOT REPRODUCE

Binary identity: `readlink -f bin/simple` =
`bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes, mtime
2026-08-16 22:59:37 (a Rust seed; it prints the seed banner). Nothing was
rebuilt or redeployed — `src/**` is read as source on every run, so this
exercises CURRENT source through that front-end.

The row's symptom is "exited 0 in about 1.4 seconds, printed nothing, and
produced no output file". Re-run against a minimal entry
(`fn main() -> i64: print("hi"); 0`):

```
$ bin/simple native-build <tmp>/nb.spl -o <tmp>/nbout
[build] source_closure 1/1 step 1/6 complete
[build] load_sources 1/1 step 1/6 complete
[build] parse 1/1 step 2/6 complete
[bootstrap-error-count] source_idx=0 point=post-store count=0
...
rc=0
ARTIFACT 23816 bytes 2026-08-17 09:26:41.856372876 +0000
```

Every element of the symptom is absent:

- **Not 1.4s.** A 115s probe timed out mid-build (`rc=124`) with live progress
  streaming; the full build needed several minutes.
- **Not silent.** Six-step `[build] …` progress plus per-point error counts.
- **An artifact exists and RUNS.** `file` reports `ELF 64-…`; executing it
  prints `hi` and exits 0. `stat` size/mtime quoted above, per the
  artifact-not-exit-code rule.

### Proving code in CURRENT source

The row itself suspected this ("Current source already contains two fail-closed
checks that the deployed artifact does not exhibit") and was right. Both are
present and are now spec-pinned:

- `src/app/cli/native_build_main.spl:270` —
  `if code == 0 and output_path != "" and not rt_file_exists(output_path):` ->
  prints `error: native-build worker exited 0 but produced no output binary:`
  plus `Treating a successful-looking exit with a missing output file as a hard
  failure.` and returns 1.
- `src/app/io/_CliCompile/compile_targets.spl:1245` —
  `if not _cli_file_exists_impl(staged_output):` rejects a driver `Success`
  whose staged output is absent.

So the defect this row names was a property of the unadmitted deployed
artifact, not of the source. Classified by CONTENT, not by SHA ancestry.

### Spec

`test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl` —
`Results: 4 total, 4 passed, 0 failed`. It asserts the ARTIFACT check itself
exists at both layers (an implementation that returns 0 without ever stat-ing
its output would pass any exit-code-based spec while shipping this exact
defect), with a non-vacuity floor on both source reads.

**Ablation (causation proved):** neutering the worker gate to `if false:` gives
`Results: 4 total, 3 passed, 1 failed`; restoring it returns 4/4.

### What is NOT retired

The render-lane unblock condition at the top of the original text — admit and
deploy a source-matched Stage 4 CLI, then build/run
`test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl` — is untouched. It needs
a deploy of the shared `bin/release/**`, which this shard was forbidden from
doing (~15 lanes share this checkout). That work belongs to
`doc/08_tracking/bug/no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09.md`,
not here: no 8K performance conclusion is drawn either way.

---

## Original 2026-08-14 record (superseded, kept verbatim)


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

