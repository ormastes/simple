# Self-hosted runtime-authority republish path (2026-08-12)

## Status

**Blocked before publication.**  Current source contains the Vulkan/JIT
runtime-symbol repair, but this tree has no provenance-admitted Stage-4
pure-Simple CLI to publish it.  A fresh Rust seed/runtime authority alone is
not a usable deployment and must never be copied into `bin/release/**`.

## 2026-08-12 current-stage observation

The separately owned `build/simpleos-enhance-current-stage2` run has now
finished its explicitly bounded `--stop-after-stage2` work with `exit-0`:

- the progress receipt records six of six tasks complete with zero failures;
- `stage2-native-build.log` records a linked Stage-2 executable after 829
  compiled units (`1721.4s` total);
- its runtime-authority executable is present under the isolated build output.

This is Stage-2 construction evidence only.  The run neither attempted Stage 3
or Stage 4 nor produced a deployment/admission receipt, so it cannot authorize
native Vulkan rendering or a `bin/release/**` replacement.

## Bounded inspection evidence

- `src/runtime/runtime_memory.c:465` defines
  `rt_struct_receiver_valid`.
- The current Rust source registers it in the runtime export scan and JIT
  manifests (`src/compiler_rust/runtime/src/lib.rs:369`,
  `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:612`).
- A fresh isolated Rust-authority product at
  `/mnt/data/bs2/final-current/bootstrap/rust-authority-4f5666c.../target/x86_64-unknown-linux-gnu/bootstrap/`
  contains the symbol in `libsimple_runtime.a` (`nm -g --defined-only`:
  `T rt_struct_receiver_valid`).  It is **not** a published self-hosted CLI.
- `bin/simple` resolves to
  `bin/release/x86_64-unknown-linux-gnu/simple`, while the deployed target is
  older than the fresh authority and is still rejected by the rendering
  native-policy gate.  One bounded 10-second `bin/simple --version` probe
  emitted no identity output; it was not retried.
- A separate authority rebuild is live as of this inspection:
  `/mnt/data/bs2/final-current/bootstrap/bootstrap-progress.state` reports
  `milestone=rust-rust-seed-build`.  Do not start another bootstrap against
  this shared target root.

## Why a direct rebuild cannot yet finish the deployment

The full CLI requires a complete Stage 2 -> Stage 3 -> Stage 4 chain.
Existing current-state evidence says that is not admitted yet:

1. `doc/09_report/verify_compiler_loader_script_crosslang_perf_2026-08-11.md`
   records no admitted current pure-Simple compiler and a current Stage-3
   attempt that ended with `functions=0` after about 981 seconds and 22 GiB
   RSS.
2. `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
   records a deterministic exit-zero but vacuous Stage-3 executable: the real
   `bootstrap_main` object was emitted beside the output rather than linked.
3. Therefore publishing the fresh Rust authority or copying its `simple`
   executable would only replace one Rust seed with another and would violate
   the repository's self-hosted provenance policy.

## Shortest safe sequence after the compiler owner fixes admission

Run these steps serially, only after the live authority builder has finished
or released its lock.  Use a new output directory; never overwrite
`bin/release/**` by hand.

```sh
# 1. First prove the concurrently built Rust authority is complete and carries
#    the exact export.  This is read-only and bounded.
nm -g --defined-only <authority>/libsimple_runtime.a | \
  rg 'rt_struct_receiver_valid'

# 2. Once Stage-2/3 non-vacuity is repaired, perform exactly one bounded,
#    provenance-owning deploy.  The wrapper atomically publishes only after
#    the staged checks pass.
timeout -k 30s 3600s sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --mode=dynload --deploy \
  --output=build/bootstrap-render-authority-20260812 \
  --progress --progress-interval=30

# 3. Verify the admitted deployed candidate once; it rejects seeds/stale
#    artifacts and runs real JIT capability probes.
sh scripts/check/check-deployed-binary-capabilities.shs

# 4. Only on PASS, run the native Vulkan gate once.  It supplies the actual
#    adapter identity and blocks interpreter fallback.
env SIMPLE_VULKAN_READBACK_TIMEOUT_SECS=75 \
  SIMPLE_VULKAN_READBACK_WORK_DIR=build/vulkan-engine2d-readback-live-20260812 \
  REPORT_PATH=doc/09_report/vulkan_engine2d_readback_2026-08-12.md \
  sh scripts/check/check-vulkan-engine2d-readback.shs
```

The 3600-second ceiling is an upper bound, not a claim that the current
compiler will converge.  Stop on the first failed stage.  Stage 2/3 acceptance
must prove that the produced executable is non-vacuous (not merely exit zero),
then Stage 4 must pass the wrapper's post-bootstrap smoke gate before the
`--deploy` swap can occur.

## Required owner work before step 2

The compiler/runtime owner must first produce one current Stage-2 and Stage-3
artifact with a nonzero real function/symbol surface and a linked
`bootstrap_main` object.  The Stage-3 `functions=0` / unlinked-object defect
is a compiler pipeline issue, distinct from the runtime-export repair.  No
rendering lane can safely bypass it.

## 2026-08-12 follow-up terminal evidence

Two later, independently owned bootstrap receipts do not change the admission
state:

- `build/simpleos-enhance-registry-stage2` finished its bounded
  `--stop-after-stage2` run with `exit-0`.  Its progress receipt reports six
  of six tasks complete with zero failures, and its Stage-2 native-build log
  records a linked `simple` after 830 compiled units (`1255.3s` compile plus
  `78.2s` link).  The isolated Stage-2 binary is present at
  `stage2/x86_64-unknown-linux-gnu/simple`.  There is no Stage-3 or Stage-4
  completion/admission/deployment receipt in that output.
- `/mnt/data/bs2/final-current/bootstrap` reached the
  `rust-rust-compiler-backfill-build` phase and the corresponding Cargo log
  says that package finished successfully.  The authoritative progress state
  nevertheless ends at `milestone=exit-1`, with a terminal failed event and
  no subsequent pure-Simple Stage-2/Stage-3/Stage-4 artifact or deployment
  receipt.  The available terminal log does not attribute the later failure,
  so this record deliberately does not infer a root cause.

Neither result authorizes native rendering.  Native Vulkan and booted SimpleOS
must remain gated on a provenance-admitted, non-vacuous Stage-3 and Stage-4
self-hosted CLI.

## 2026-08-12 isolated Stage-4 terminal receipt

`/mnt/data/bs2/final-stage4-36be8a` completed its bounded Stage-4 native
build at `2026-08-12T04:05:06Z`: `logs/stage4.log` records a linked
`output/simple` (815 compiled, zero cached, zero failed) and the wrapper
exited `0`. The candidate is nevertheless **withheld**, not admitted or
deployed. Its terminal summary records different before/after compiled-root
manifests and the explicit reason
`compiled_source_changed_during_build`.

That fail-closed result is expected in this concurrently edited worktree.
Do not copy the candidate into `bin/release/**` and do not run native Vulkan,
booted-SimpleOS, or 8K evidence gates from it. A later owner-controlled
Stage-4 run must start from a stable compiled-root snapshot and pass its
postflight admission before deployment and capability checks can resume.

## 2026-08-12 stable-seal Stage-4 smoke failure

`/mnt/data/bs2/final-stage4-receipt-550fe7` subsequently produced a second
Stage-4 candidate with `source_seals_unchanged=yes` and a linked 815-unit
binary. Admission is still denied: its essential-tools smoke returned `1`.
The authoritative log records `validate_json_valid_rc=1` and
`error: unknown command 'run'` while invoking the isolated candidate under
`SIMPLE_NO_STUB_FALLBACK=1`.

This is a concrete CLI capability/admission defect, not a rendering failure.
Keep `bin/release/**` unchanged. The compiler owner must restore the admitted
candidate's `run` command before repeating capability, Vulkan, boot, or 8K
gates.

## 2026-08-12 closure-fix propagation terminal failure

`/mnt/data/bs2/closure-fix-propagation-078b0b` held its immutable curated
manifest steady, but its Stage-4 native build exited `1` before producing a
candidate. The terminal receipt identifies exactly one failure:
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` exceeded the
native build's per-file 60-second compilation cap. Its subsequent probe gate
did not start (`step_b=not_started_probe_gate_unsatisfied`).

This is a compiler compilation-time blocker, distinct from the resolved
`src/app/doc/**` entry-closure exclusion. No candidate exists and neither
deployment nor rendering evidence is authorized. The compiler owner must
reduce/partition that module's compilation work or revise the bounded
per-file strategy with measured justification before another admission run.

### Root-cause diagnosis (read-only, 2026-08-12)

The stable candidate is not merely missing a dispatch-table row.  The current
source has the `run` branch in
`src/app/cli/_CliMain/main_and_help.spl:501` and the table row in
`src/app/cli/dispatch/table.spl:520`; `cli_handle_run` is implemented in
`src/app/io/_CliCommands/handler_commands.spl:165`.

The candidate itself proves that the wrong entry object was linked:

- `nm` exposes `app__cli__bootstrap_main__run_native_build_bootstrap` and no
  full-CLI command-dispatch body; its sole `"error: unknown command"` string
  is the one from `src/app/cli/bootstrap_main.spl`.
- Disassembly of the candidate's exported `spl_main` calls
  `app__cli__bootstrap_main__run_native_build_bootstrap` for `native-build`
  and implements the bootstrap-only `--version`/`compile` parser.  This
  exactly explains `error: unknown command 'run'`.
- The Stage-4 producer deliberately leaves `SIMPLE_BOOTSTRAP=1` set while
  setting `SIMPLE_BOOTSTRAP_STAGE4=1`.  In
  `src/compiler/80.driver/driver_aot_native_output.spl`,
  `_compile_selected_module` currently treats **every** such build as a
  bootstrap-object build: after compiling each module it copies the global
  `llvm_bootstrap_last_object_path()` instead of writing that module's returned
  `module.object_code`.  The last bootstrap object therefore supplies
  `spl_main`, even though the requested Stage-4 entry is
  `src/app/cli/main.spl`.

**Exact owner fix:** `src/compiler/80.driver/driver_aot_native_output.spl`.
Restrict the global bootstrap-object copy branch to bootstrap stages only
(`SIMPLE_BOOTSTRAP=1` **and** `SIMPLE_BOOTSTRAP_STAGE4 != 1`).  The Stage-4
branch must write each `CompiledModule.object_code` at its module-specific
path, preserving the explicitly selected CLI entry's `spl_main`.  Do not alter
the Stage-2/Stage-3 bootstrap-object behavior.

**Required regression proof:** add a source contract beside
`test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl` that
requires the object-copy condition to exclude `SIMPLE_BOOTSTRAP_STAGE4=1`,
then run one isolated Stage-4 candidate through
`check-bootstrap-essential-tools-smoke.shs`.  Admission remains denied until
the latter reaches the terminal essential-tools receipt.

## 2026-08-12 isolated Stage-3 terminal receipt

`/mnt/data/bs2/corrected-stage3-f3d639` now contains a terminal Stage-3
native-build receipt: `logs/stage3.log` records a linked
`output/simple` (127174 KiB), with 815 compiled, zero cached, and zero failed
units (`1435.5s` total).  Its postflight manifest records the required
bootstrap/runtime source guards as `OK`, and `logs/version.log` identifies
the resulting executable as `simple-bootstrap 1.0.0-beta`.

This is materially stronger than the earlier vacuous `functions=0` receipt,
but it is not a deployment receipt.  At inspection time a distinct bounded
Stage-4 invocation was already live at
`/mnt/data/bs2/final-stage4-36be8a`, using precisely this Stage-3 executable
and its Stage-2 runtime authority.  Do not start another Stage-4 or copy this
candidate into `bin/release/**`; wait for that invocation's terminal
postflight/provenance result before admitting native rendering checks.

## 2026-08-12 isolated full-CLI terminal failure

The separate bounded build at `/mnt/data/bs2/final-full-cli-078b0b` is
terminal: no matching build process remained at inspection, and its
`logs/build.log` ends at phase 1 with:

```
[ERROR] phase 1 FAILED
error: focused native-build: import 'app.doc.public_check.statistics' (used in src/app/cli/check_capsule.spl) resolved to 'src/app/doc/public_check/statistics.spl' but that file is empty or excluded from compilation
```

No `bin/simple` candidate or admission/essential-tools-smoke receipt exists
under that isolated root. Its curated-manifest preflight completed its listed
source-contract checks, but that does not admit the failed compiler output.
The owner must restore or include the `app.doc.public_check.statistics` module
in the full-CLI native-build source closure, then run a fresh bounded build;
do not copy or deploy any artifact from this failed attempt.

### Exact Phase-1 import-filter root cause (read-only, 2026-08-12)

`src/app/doc/public_check/statistics.spl` is neither empty nor missing: it is
the 311-line source file whose current digest is
`09f40d50edbad58e93bfb0958958f48aa8aef5bc8b04da63326683274ee2e064`.
Its path derives canonically to `app.doc.public_check.statistics`, so the
import in `src/app/cli/check_capsule.spl` is correct and has no alias mismatch.

The actual exclusion is in the compiler owner
`src/compiler/80.driver/driver_source_loading.spl`:
`_driver_collect_entry_import_source` returns an empty source list for every
path containing `/doc/`.  The resolved production path
`src/app/doc/public_check/statistics.spl` matches that broad filter, and the
Phase-1 caller consequently emits the misleading "empty or excluded" error.

**Minimal owner fix:** preserve exclusion of repository documentation trees but
allow explicitly imported production modules under `src/app/doc/` in
`_driver_collect_entry_import_source` (and keep the bulk-root filter unchanged).
Use normalized path identity so both `src/app/doc/...` and absolute-worktree
spellings are admitted; do not rename the module or weaken test/fixture/doc
exclusions generally.

**Focused regression:** extend
`test/01_unit/app/cli/bootstrap_main_source_spec.spl` beside its existing
explicit-import collector test to call
`_driver_collect_entry_import_source("src/app/doc/public_check/statistics.spl")`,
assert a nonempty result, and assert its module name is exactly
`app.doc.public_check.statistics`.  Then repeat only the isolated full-CLI
Phase-1 build before a broader Stage-4 retry.

## 2026-08-12 propagated full-CLI terminal host-safety stop

The separately owned propagated full-CLI run at
`/mnt/data/bs2/final-full-cli-propagated-078b0b` is terminal.  Its immutable
preflight records `entry=src/app/cli/main.spl`, 2,457 closure sources, a
300-second per-file cap, and unchanged curated-manifest and producer digests.
It began at `2026-08-12T05:52:04Z`; the terminal receipt records
`status=stopped_for_host_safety` and `reason=phase2_parse_memory_runaway` at
625 seconds and 33,885,788 KiB (32.32 GiB) RSS.  The shell time receipt says
the build command was terminated by signal 2 after 673.41 seconds.

The terminal receipt explicitly records `candidate=absent`, `cache_files=0`,
`canonical_provenance=not_generated`, `essential_tools_smoke=not_run`, and
`post_bootstrap_sspec=not_run`; `output/` is empty.  Consequently this attempt
proves none of the full CLI's `run`, `check`, or `native-build` capabilities
and supplies no self-hosted authority admission.  Its receipt marks retry as
forbidden; do not reuse, deploy, or capability-test an artifact from this
root.  The compiler owner must address the Phase-2 parse-memory growth before
any fresh, independently bounded full-CLI admission attempt.

## 2026-08-12 bounded Stage-4 parse-memory probe design (read-only)

The propagated receipt already separates the first boundary: Phase 1 finished
the 2,457-source closure in 25.521 seconds (`heap_registry=2109531`), while
the 32.32 GiB stop happened only after Phase 2 began. That prioritizes the
streaming parser/surface path but does not identify parser work, surface
promotion, or release ownership. Do not relaunch the full CLI to answer that.

### Provenance-safe diagnostic, not a forged candidate

`check-stage4-selfhost-parse-memory-multifile.shs` cannot be the next command:
it requires an adjacent Stage-4 provenance manifest, and that manifest is
written only after the candidate's essential-tools smoke. A stale/failed-smoke
candidate or an operator-authored manifest would defeat its contract. Use a
separately labelled **pre-admission diagnostic** bound to a verified Stage-3
parent; it is never deployable and cannot satisfy a rendering/native gate.

Preconditions: (1) a canonical non-symlink Stage-3 parent plus verified Stage-3
manifest, all checked against a private immutable source copy; record canonical
paths and SHA-256s for parent, Stage-3 manifest, runtime directory, producer,
and runner; (2) a sealed real-CLI closure manifest of `(ordinal, physical path,
content SHA-256, canonical module)`, rechecked at termination; (3) private
cache/output roots, `SIMPLE_NO_STUB_FALLBACK=1`, one compiler process group,
positive host/swap headroom, and no competing Stage-4/`simple` compiler; and
(4) the truthful Stage-4 AOT profile (bootstrap, Stage4, entry closure,
low-memory, streaming surfaces, one thread, core-C runtime). A Rust seed,
`bin/simple`, old Stage-4 output, cache reuse, or an operator-authored Stage-4
manifest is rejected.

### Attribution records required before the run

The streaming branch currently emits the release receipt only to stderr; a
killed worker can lose the `parse:file:start/done` trail. Add an append-only,
once-per-event **phase-profile-file** record (not a stdout/stderr duplicate)
with `seq`, canonical path, `heap_registry`, `heap_live_bytes`, and
`heap_peak_bytes` for:

```
phase1:closure:done
phase1:load_sources:done
phase2:streaming:file:start
phase2:streaming:file:parsed
phase2:streaming:file:surface-added
phase2:streaming:file:surface-promoted
phase2:streaming:file:released
phase2:streaming:probe-complete
```

All per-file records share contiguous sequence/path identity; `released` is
legal only after transient-scope end succeeds. Missing, duplicate, out-of-order
or unsealed-path records invalidate the diagnostic. With one-second
process-group RSS samples joined to the last durable marker, growth before
Phase-1 completion identifies closure scanning; `start`→`parsed` identifies
parser/AST work; `parsed`→`promoted` identifies surface extraction/promotion;
and post-promotion growth without `released` identifies failed release.

### Fixed first run and acceptance

The probe must parse only the first **12 unique physical sources** of the sealed
real `src/app/cli/main.spl` closure, then terminate with an explicit
`parse_probe_complete` marker without HIR/MIR/codegen/linking. A synthetic chain
is insufficient because it has previously missed real source-feature effects.
The runner has hard group budgets of **180 seconds** and **3,145,728 KiB
(3 GiB)** RSS, sending TERM then KILL after ten seconds. Any external OOM or
earlyoom event is `host-contaminated`, not a compiler verdict.

A passing receipt requires Phase-1 terminal markers within 45 seconds; exactly
12 identity-matching records at every streaming sub-phase and 12 releases; no
parser/OOB/stale-generation diagnostic; RSS below 3 GiB at every release; no
adjacent four-release RSS increase above **512 MiB**; and no
`start`→`released` increase above **256 MiB** for one source. Heap-registry
deltas are reported, not used as the sole memory proxy. These are deliberately
generous tripwires against the observed 32.32-GiB/nine-release stop. A PASS may
justify the existing provenance-admitted 40-file gate, but never authorizes a
Stage-4 candidate, deployment, Vulkan, SimpleOS, or 8K claim.

### 2026-08-13 Stage-3 native parser crash

The bounded `packed-memory-build9` authority attempt completed Stage 2, then
loaded all 847 Stage-3 sources and exited **139** while beginning the second
streaming parse. Its durable replay records `bootstrap_main.spl` as source one
and `driver.spl` as source two. The retained core backtrace is deterministic:
`parser_init_with_path -> ast_reset -> _ast_harden_retire_snapshot ->
ast_gen_harden_enabled`, faulting while dereferencing the optional hardening
gate's module-array cache.

The repair removes that cache: the gate runs only during `ast_reset`, so it now
reads `SIMPLE_AST_GEN_HARDEN` directly from its environment owner. The arena
retirement semantics and the gate's default-off behavior are unchanged. The
native arena source contract additionally rejects reintroduction of the cache.
This is static/source evidence only. A fresh frozen Stage-2/Stage-3 authority
run must reproduce the two-source transition without a crash before any later
admission or rendering evidence is considered.

The immediately adjacent `ast_decl_mode_slot` had the same one-element-array
cache shape and is enabled by `SIMPLE_NATIVE_ARENA_DECLS=1` in Stage 3. It is
now a scalar `-1/0/1` cache: native code keeps its per-declaration fast path,
while a non-persistent interpreter state falls back to the existing direct
environment lookup. This removes the next reachable reset-crossing aggregate
hazard without changing the arena-preferred mode decision.

The subsequently launched Stage-2-only run at
`/mnt/data/.simple/bootstrap/perf-stage2-a899e7b16b5-20260813` does **not**
meet that condition: its source root `/mnt/data/perf-feature-integrated-current`
still contains `ast_gen_harden_slot` and calls `ast_gen_harden_refresh()` from
`ast_reset`. It is a pre-repair snapshot and cannot validate or admit the
repair above. Do not resume Stage 3 from that output; make a new frozen source
copy only after the repair is present and its source identity is recorded.

### 2026-08-13 frozen receiver-authority Stage 2

The current bounded authority run uses the clean frozen checkout at
`fc7a49de87f9367c0bb826535b95fa4fc9c2780e` and writes only beneath
`/mnt/data/.simple/bootstrap/receiver-stage2-fc7a49de-20260813`. It is
pre-admission until it emits a passing Stage-2 sanity receipt, matching
source/Git/tool after-snapshots, and both canonical receiver receipts:
`stage2-struct-receiver-smoke.env` and
`stage2-llvm-struct-receiver/receipt.env`. There is no canonical
`stage2-receiver.env`; do not substitute or invent one.

The LLVM receipt is intentionally stronger than runtime symbol availability:
it binds the retained IR declaration and call, the generated object's undefined
import, linked executable provider, and execution of immutable receiver methods
with zero and one explicit argument against the frozen runtime. Stage-3 resume
must run from this same frozen checkout and revalidate both receipts along with
the admitted snapshots before writing its manifest. No deployment or rendering
claim follows from an in-progress or failed Stage-2 run.
