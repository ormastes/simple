# Bootstrap `bootstrap_main` native build makes no object progress

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Observed

On 2026-07-23, the bootstrap-only Rust seed ran this no-stub shard for more
than 15 minutes at about one CPU and 1.5 GiB RSS without producing an object:

```sh
SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --backend cranelift \
  --source src/compiler --source src/app --source src/lib --entry-closure \
  --threads 8 --cache-dir build/mini_cache_bootstrap_flat_globals \
  --mode dynload --entry src/app/cli/bootstrap_main.spl \
  -o build/native_probe/simple_bootstrap_flat_globals
```

The log stopped changing after import/GC warnings. The process remained
CPU-active with a defunct child and zero cached `.o` files, so the repo runaway
guard required termination. Temporary log and empty cache were removed.

On 2026-07-25, after the CLI global-flag parser split (`4392ce6...`) and
repo-local seed fallback (`debc189...`), a clean workspace
`/home/ormastes/dev/pub/simple-redeploy-clean` reproduced the same pre-object
state:

- Main CLI probe:
  `SIMPLE_NO_STUB_FALLBACK=1 /home/ormastes/dev/pub/simple/bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib --entry-closure --threads 8 --cache-dir build/bootstrap/native_cache --mode dynload --entry src/app/cli/_CliMain/main_and_help.spl -o build/native_probe/simple`
  hit a 240s cap with zero log lines and zero cached `.o` files.
- Bootstrap shard:
  `SIMPLE_NO_STUB_FALLBACK=1 /home/ormastes/dev/pub/simple/bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib --entry-closure --threads 4 --cache-dir build/mini_cache_bootstrap_main --mode dynload --entry src/app/cli/bootstrap_main.spl -o build/mini_builds/bootstrap_main/simple_bootstrap`
  hit a 180s cap with zero log lines and zero cached `.o` files.

No child process from those clean-workspace probes remained afterward. An
unrelated MCP mini build was active in `/home/ormastes/dev/pub/simple` and was
left untouched.

Later on 2026-07-25, `src/app/cli/native_build_main.spl` was made worker-only
so the parent entry no longer imports `app.io._CliCompile.compile_targets`
before it can spawn the worker. Evidence:

- `simple_seed run src/app/cli/native_build_main.spl --help` returned in 0.05s
  with the help text, proving the parent entry no longer loads the compiler graph
  just to start.
- The corrected worker-parent shard still hit a 180s cap with only the seed
  warning in its log, zero cached `.o` files, and no output binary:
  `SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_BUILD_FORCE_WORKER=1 simple_seed run src/app/cli/native_build_main.spl --backend cranelift --source src/compiler --source src/app --source src/lib --entry-closure --threads 4 --cache-dir build/mini_cache_bootstrap_main_worker_parent --mode dynload --entry src/app/cli/bootstrap_main.spl -o build/mini_builds/bootstrap_main_worker_parent/simple_bootstrap`.

The blocker has moved from parent-entry graph loading to the worker process
itself producing no progress/output before the timeout.

## 2026-07-25 resolution

The pre-object entry-closure stall was caused by two costs in dependency
discovery:

- copy-on-write text buckets were used as a set/cache;
- every source line was trimmed and parsed even when it could not contain a
  dependency declaration.

The implementation now reuses the mutable `HashSet`/`HashMap` collections and
prefilters lines for `use `, `mod `, `import `, or `export ` before parsing.
Representative source scans improved by 28-58x. The isolated closure probe
completed all 396 files in 42.39 seconds, and the bounded direct worker reached
`Entry closure files: 396` and `Driver start`.
The retained cycle-3 worker log proves the latter progress markers; the
42.39-second isolated timing was observed interactively and has no retained
timing log.

The closure blocker is resolved. The worker then exposed the separate
Stage 2 interpreter failure tracked in
`bootstrap_stage2_interpreted_parser_empty_array_2026-07-24.md`; no pure-Simple
CLI artifact has been admitted yet.

## Expected

The shard should either emit cached objects/its executable or fail with a
specific diagnostic within the bootstrap verification window.

## Follow-up

Continue from the Stage 2 interpreter bug. Reuse the bounded worker command
with its isolated cache and keep `SIMPLE_NO_STUB_FALLBACK=1`; do not repeat the
now-resolved entry-closure profiling cycle.

## 2026-07-26 native incremental follow-up

The retained native pure-Simple compiler bypassed the seed-interpreter timing
wall and parsed the standalone driver closure in 44 seconds. It then failed
specifically on `pub mod` declarations because the parser's visibility
dispatcher handled public functions, types, values, uses, and exports but
omitted the existing soft-keyword `mod` path.

`parse_module_decl_with_visibility` now lowers `pub mod` through the same
relative sibling import representation as private `mod`; the focused parser
regression passes 1/1. A temporary private-`mod` bridge let the older compiler
consume the fixed parser source and parse the full closure in 65 seconds, but
that generation segfaulted while lowering `src/compiler/80.driver/main.spl`
in HIR. Canonical `pub mod` source was restored immediately and no bridge
artifact was retained. The next incremental generation must start from a
compiler that has the existing standalone-main HIR repair; do not return to
the seed-interpreted closure path.

## 2026-07-26 retained compiler MIR follow-up

A one-file explicit-return `main` probe proved HIR lowering completes before
the retained compiler crashes in `CompilerDriver.lower_to_mir`. GDB places the
fault immediately after `MirLowering.lower_module` returns; the phase log shows
the returned function dictionary already has invalid length `-1`.

The next statement was a duplicate driver-side traversal that recopied VHDL
metadata from HIR into the returned MIR aggregate. `MirLowering.lower_module`
already preserves that metadata in both bootstrap and normal paths, and the
VHDL design catalog also reconciles HIR provenance. The duplicate traversal is
removed, with an executable regression asserting the lowerer retains hardware
metadata. Resume through one cache-preserving bootstrap-mode incremental
generation so the old binary does not re-enter its broken normal MIR transport.

Three bounded generation attempts used the retained cache without reset:

1. Legacy expression-environment mirroring aborted on a NUL string literal.
2. `SIMPLE_NATIVE_ARENA_DECLS=1` removed that transport and parsed the closure
   in 47 seconds, then stopped at the old binary's known `pub mod` gap.
3. A temporary private-`mod` bridge parsed all 546 closure sources in about
   63 seconds, entered real bootstrap HIR, and segfaulted while lowering
   `run_compile_bootstrap`.

Canonical `pub mod` declarations were restored and no bridge artifact exists.
The three-cycle cap is reached. Resume by isolating the expression in
`run_compile_bootstrap` that trips the old HIR lowerer; retain native arenas,
the current cache, and `SIMPLE_NO_STUB_FALLBACK=1`.

## 2026-07-26 aggregate bridge isolation

The next bounded session tested three non-equivalent bridge entries:

1. Replacing only `run_compile_bootstrap` let that function and `main` finish
   HIR, then the general `run_native_build_bootstrap` body segfaulted.
2. A fixed-purpose entry calling `aot_native_file_with_backend` finished its
   own HIR, then segfaulted at the helper's initial mutate-after-default
   `CompileOptions` construction.
3. Inlining a complete immutable `CompileOptions(...)` literal removed that
   helper and segfaulted while lowering the entry's literal itself.

All runs used native arenas, the retained cache, and
`SIMPLE_NO_STUB_FALLBACK=1`; all parsed the closure and reached real HIR.
Canonical `bootstrap_main.spl` and public module declarations were restored,
and no bridge artifact exists. The failure is now classified as old-generation
bootstrap aggregate HIR transport, not CLI dispatch. Do not run another bridge
generation until a focused aggregate-construction regression and source repair
exist.

## 2026-08-17 scope audit — BLOCKED, and no longer a CLI-entrypoint bug

Reviewed by the lane that owns `src/app/cli/native_build_main.spl` and
`src/app/cli/bootstrap_main.spl`. A full bootstrap / native-build shard was
**forbidden this session** (a live bootstrap owned the host), so the "no object
progress" symptom was deliberately not re-attempted. Classified by CONTENT.

**This doc has already walked itself out of these two files.** Its own later
sections record the migration:

1. Parent-entry graph loading — RESOLVED, and still resolved at tip.
   `src/app/cli/native_build_main.spl` imports only `app.io.env_ops` and
   `app.io.process_ops` (lines 3-4). It does **not** import
   `app.io._CliCompile.compile_targets` or anything under `compiler.driver`; its
   only heavyweight action is spawning `src/app/cli/native_build_worker.spl` as a
   subprocess (line 247). The `--help` fast path (382-384) returns before any
   spawn, matching the recorded 0.05s measurement.
2. Entry-closure discovery cost — recorded RESOLVED (2026-07-25).
3. The blocker then moved to the Stage 2 interpreter, then to `pub mod` parsing,
   then to MIR transport, and the doc's **own final section** (2026-07-26
   aggregate bridge isolation) concludes: *"The failure is now classified as
   old-generation bootstrap aggregate HIR transport, not CLI dispatch."*

That final classification puts the live defect in HIR/MIR aggregate construction
(`CompileOptions` mutate-after-default and literal lowering), i.e. under
`src/compiler/20.hir/**` and `src/compiler/50.mir/**` — paths this lane must not
touch and which other lanes own.

**The one thing this lane can still assert** is that `bootstrap_main.spl` never
reports success without a real artifact, which is the failure mode that would
make a non-progressing shard look green. Both in-process lanes check
`file_exists(output)` and reject an artifact of <= 300 bytes
(`bootstrap_main.spl:342-348` for native, `443-450` for SMF). Pinned by
`test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl`
("never reports in-process native-build success without a real artifact").

### What could NOT be proven this session
- Whether the entry-closure shard now produces objects. No bootstrap or
  native-build shard was run.
- Whether the aggregate-HIR segfault at `run_compile_bootstrap` /
  `run_native_build_bootstrap` still reproduces on a current compiler.
- Any timing claim (42.39s closure, 396/546 files) — none re-measured.
- The recommended next action is unchanged and remains a bootstrap-lane task:
  isolate the aggregate construction that trips HIR lowering, with a focused
  regression, before another bridge generation.
