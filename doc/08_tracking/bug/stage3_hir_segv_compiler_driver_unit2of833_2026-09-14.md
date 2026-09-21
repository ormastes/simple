# Stage 3 native-build SEGVs in the HIR phase at unit 2 of 833 (`compiler.driver.driver*`)

## Round 28 (2026-09-21) — macOS retained HIR cache lifetime identified

Scope: native `aarch64-apple-darwin` only. Base `c71a262f5f8`, rebuilt through
the canonical Stage 2 admission lane. This does not establish the cause or
resolution of another host's historical failures.

A single entry importing `compiler.driver.driver_public_api.{interpret_file}`
reduces the failure to 30 modules. HIR finishes the entry and then stalls at
`driver_public_api.spl` (`done=1 total=30`, roughly 490 MiB RSS). A native
`sample` capture places the loop in `HirLowering.reexport_root_memo_lookup`,
calling `rt_array_get`. An ordinary two-module function import completes.
The scalar name-index operations also pass when compiled in isolation.

The streaming driver creates one `HirLowering` before the module loop.
`lower_streaming_surface_source` then opens and ends a transient allocation
scope for each file. It promoted the HIR result, diagnostics, flat HIR row,
and frontend registries, but omitted the resolution caches that
`begin_module` deliberately retains. In particular, the first re-export
query replaces its memo arrays inside the first transient scope. Ending that
scope frees those arrays. A subsequent hash-chain lookup reads freed array
handles; invalid reads become nil and then index zero, so the chain need not
terminate. Retained dictionaries and dynamic key strings have the same
ownership omission.

The proposed fix adds `promote_resolution_caches_transient_owner` and invokes
it while the scope is paused, before teardown. Its explicit root set covers
the package, declaration, sibling, explicit dependency, payload miss, impl,
name, glob miss and re-export caches, including their scalar mirrors.
Importer symbol tables and temporary lowering graphs remain reclaimable.
The importer-specific `imported_enum_owner_rows` mirror is now reset with
its companion dictionaries in `begin_module`.

Regression artifacts:

- `test/fixtures/hir_resolution_cache_scope/main.spl`: cross-module function
  signature with a separate result-type owner; must compile and print
  `hir-resolution-cache-scope-ok`.
- `test/01_unit/compiler/hir/hir_resolution_cache_transient_owner_spec.spl`:
  two native transient scopes, retained negative results and dynamic text,
  rejection outside a paused scope, and importer-local owner-row cleanup.

### Focused verification (2026-09-21)

Patched Stage 2 was admitted on macOS arm64. Binary SHA-256:
`3d888a91386a1c18e8ad2851b3d46d669862b2871ca43ac4490e6ca1ff215a65`.

- The 30-module reduction clears the former stall: `driver_public_api.spl`
  advances from HIR done 1 to done 2 in 13 ms. It subsequently exits 1 with
  48 unresolved-import diagnostics from its incomplete dependency closure.
  This establishes progress past the sampled loop, not a successful build.
- The three-file fixture compiles, links in 8.041 s, and prints
  `hir-resolution-cache-scope-ok`, exit 0. Its imported function signature
  refers to the separately owned struct; the executable checks a scalar
  function result to avoid conflating ownership with aggregate ABI behavior.
- An earlier struct round-trip variant reached all five HIR module aliases
  but aborted in native codegen (exit 134): `unsupported LLVM value conversion
  from double to ptr`. The variant constructed `ResultValue(code: 42)`,
  passed it through `round_trip(value: ResultValue) -> ResultValue`, then
  read `.code` via `result_code(value: ResultValue) -> i64`. This remains an
  open backend issue, not a grammar workaround or a claimed fix.
- The separate `transient_lifetime.spl` native fixture exercises two paused
  scopes, promoted cache arrays and newly appended text. Its first native
  compile exits 1 with `compiled unit has no usable capsule result:
  identity-invalid`; no executable or lifetime PASS is claimed.
- The compiler-only Stage 2 does not execute the SSpec runner. The new unit
  spec remains unexecuted. Canonical Stage 3 is pending a frozen-tree receipt
  after syncing newer main; a preflight receipt mismatch is not a Stage 3
  compiler result.

The successful fixture used the pure-Simple bare positional entry route:

```sh
SIMPLE_BOOTSTRAP=1 \
SIMPLE_BINARY="$PWD/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple" \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
SIMPLE_STAGE3_STREAMING_SURFACES=1 SIMPLE_NATIVE_ARENA_DECLS=1 \
SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
SIMPLE_RUNTIME_PATH="$PWD/.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-runtime-authority" \
sh scripts/bootstrap/run-process-group-timeout.shs 120 3 \
  .simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple native-build \
  test/fixtures/hir_resolution_cache_scope/main.spl \
  --backend llvm --runtime-bundle core-c-bootstrap \
  --cache-dir build/native_probe/three-module-final-cache \
  --runtime-path .simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-runtime-authority \
  -o build/native_probe/three-module-final
build/native_probe/three-module-final
```

For the lifetime probe the entry was `transient_lifetime.spl`, cache suffix
`lifetime-cache`, and output suffix `lifetime`. For the 30-module probe the
entry was `build/native_probe/import_root/main.spl`, importing
`compiler.driver.driver_public_api.{interpret_file}` with a zero-returning
`main`. Evidence is retained under `build/native_probe`: `import_root/sample.txt`,
`import_root/native.log`, `import_root/patched.log`, `three-module-after.log`,
`three-module-final.log`, and `lifetime.log`.

Status: fix implemented with focused import regression passing; full macOS
Stage 3 and native lifetime spec verification remain pending.
Tracking row: `stage3_macos_hir_resolution_cache_lifetime_2026_09_21` in
`doc/08_tracking/bug/bug_db.sdn`.

- **Filed:** 2026-09-14
- **Status:** OPEN — blocks every Stage 3 / Stage 4 / deploy on macOS arm64
- **Tree:** `origin/main` `4f4d0e12832` (includes #951, #952, #955, #968)
- **Lane:** F74 round 3, macOS arm64, worktree `agent-affc884d75d16fbde`

## Symptom

`--resume-stage3-from-admitted` dies after ~23 minutes:

```
error: Stage 3 native-build failed (shell=139 worker=absent effective=139
       class=shell-signal-exit signal=signal-number-11 route=direct fallback=none)
```

`stage3-native-build-status.env`: `status=fail shell_exit_status=139
diagnostic_class=shell-signal-exit signal_identity=signal-number-11`.

## Crash point

From `stage3-native-build.log` (preserved at `build/f74logs/stage3-run5-native-build.log`),
lines 11971-12072 — the HIR phase, second unit of 833:

```
[build] phase=hir ... done=1 total=833 ... current=app.cli.bootstrap_main        <- succeeded
[build] phase=hir ... done=1 total=833 remaining=832 ... current=compiler.driver.driver
scripts/check/lib/bootstrap-stage3/command-snapshot.shs: line 274:
  69063 Segmentation fault: 11  env -i "HOME=$bootstrap_stage3_r...
```

The process that dies is the admitted Stage 2 compiler
(`.../stage3/aarch64-apple-darwin/stage2-admitted/simple`), SEGV, no diagnostic
of its own.

## This is forward progress, not a regression

The previous run of this lane (tree `def2a9c30a1`) failed earlier and
differently: 12 HIR lowering errors of the form

```
error: in-process native-build: HIR lowering error in src/app/cli/bootstrap_main.spl:
  imported enum `UnaryOp` has no declaration owner
```

PR #952 fixed exactly that. On `4f4d0e12832` the count of
`has no declaration owner` in the build log is **0**, and
`app.cli.bootstrap_main` now lowers successfully. The chain advanced past that
defect into this one.

## Not diagnosed

No core dump was captured and the crashing unit was not narrowed below
`compiler.driver.driver*`. Two sibling records filed the same day describe
Stage-2-compiler SEGVs in a different shape
(`stage2_native_method_scoped_dict_field_write_segfaults_2026-09-14.md`,
`stage2_native_class_field_text_dict_owner_lost_2026-09-14.md`); whether this is
the same root cause is **unverified**.

## Consequence

No Stage 3 artifact, therefore no Stage 4 and no deploy. `bin/release/` is
untouched; no binary was published and nothing was forged.

## Round 22 (2026-09-17, macfix lane) — main self-heals: stage2 GREEN unmodified; mac blocker was rustup default channel

Fresh worktree build/mac-boot at origin/main (630593d6082 family, includes
#1052/#1059 BOOT-20 HIR fixes) with CORRECT per-worktree git wiring
(git worktree add, not the miswired build/main-verify):

- Fingerprint stage initially refused: resolver requires rustup default
  toolchain to start with the policy channel prefix; this Mac had
  default_toolchain=stable-aarch64-apple-darwin vs policy channel=nightly
  (src/compiler_rust/rust-toolchain.toml). `rustup default nightly` fixed it.
  Trace: settings-host=parse-fail in bootstrap_stage3_installed_rust_toolchain.
- Stage2 then compiled the FULL Simple tree with ZERO hir Type mismatches
  (0 errors, 535s compile + 14.8s link) — the da8964fe990 seed HIR
  regression this lane filed on PR #1038 is cured on main. Admission
  (verify-landed-compiler-fix) + resume git-state gates PASSED (the fresh
  worktree's git correctly measures its own tree).
- Stage3 in flight; 0 errors so far; stage2 binary contains no rt_stat_*
  symbols and linked anyway => the round-19 D2 stat gap does not bite on
  current main either.

Consequence: the share-fixes branch (3 import one-liners + D2 stub, pushed
as fix/mac-stage2-tail-units-20260917) is largely SUPERSEDED by main. Kept
value assessment pending stage3 verdict; PR will note supersession where
applicable rather than land redundant hunks.

## Round 23 (2026-09-17, macfix lane) — stage3 native-build SEGV (signal 11) at 80.driver/bootstrap_api_fixed.spl

Chain r2 got further than any prior mac lane run: admission + resume gates
PASSED (fresh worktree git wiring is sound), stage3 build ran 19.7 min,
compiled 26/826 hir modules clean, then the stage2-built simple binary
segfaulted (signal 11, exit 139, shell=139 worker=absent route=direct) in
phase3:hir:imports on src/compiler/80.driver/bootstrap_api_fixed.spl (70
lines; imports compiler.driver.driver, bootstrap_api_low_memory,
driver_core_modes, driver_compile_options, driver_compile_result).
Prior-art check: no matching record in doc/08_tracking/bug on main
(export_star_glob_partially_registers_kinds_2026-09-16.md exists only as a
sibling-lane working file, not on main). Single-file repro via stage2 binary
fails earlier at scv package-index admission (needs SIMPLE_PACKAGE_INDEX_COLD_INIT
env the real run sets) — no standalone segv.
r3 = full stage3 resume from cache to test determinism. Round 24: verdict +
minimized repro if deterministic.

## Round 24 (2026-09-17, macfix lane) — SEGV is NOT file-deterministic; load-corruption suspected; r4 final cycle

r3 (stage3 resume, default config) ALSO segfaulted (signal 11) but at a
DIFFERENT file: src/compiler/80.driver/driver.spl at +2384643ms, done=1/826
(counter view differs from r2's done=26 at +1183074ms — parallel scheduling
order differs per run). Immediately preceding the crash, repeated
[hir-reexport-chase-unresolved] warnings for facade compiler.mir.mir_lowering_types
item=Option and facade compiler.types._TypeLayout.layout_core item=text with
importer=driver.spl. Both crashes: phase3:hir, importer-resolution machinery,
~20-40 min into the run, while the machine was heavily loaded (load avg
13-31; push gates + parallel agent lanes). No macOS crash report (process
runs under env -i). No lldb capture available without modifying the
authority-bound wrapper scripts (source snapshot is admission-pinned).
SIMPLE_NATIVE_BUILD_THREADS is already 1 at resume; the compiler's internal
task pool still shows task_total=6, so there is no lower-parallelism config
to try. r4 = same resume on the now-quiet machine (load ~4): if it still
crashes, defect is a genuine self-host HIR import/reexport bug (likely
use-after-free in the re-export chase); if it passes, corruption under load.
Per the 3-cycle cap, r4 is the last attempt; findings escalate to the PR
thread + tracking either way.

## Round 25 (2026-09-17, macfix lane) — VERDICT: self-hosted compiler HIR-phase defect, 3-for-3 crashes, cycle cap reached

r4 (quiet machine, load ~4.7, identical config) segfaulted a THIRD time at a
THIRD file: src/app/cli/native_build_main.spl (+1455375ms, done=4/826).

Crash matrix (all signal 11, phase3:hir, route=direct):
- r2: 80.driver/bootstrap_api_fixed.spl, done=26, load 13-31
- r3: 80.driver/driver.spl, done=1,   load 13-31
- r4: app/cli/native_build_main.spl,  done=4,  load ~5
Every run: hundreds (508 in r4) of [hir-reexport-chase-unresolved] warnings
immediately precede the crash; chase visits facades that "neither declare
this name nor route it through a resolvable re-export".

Conclusions:
1. NOT macOS-environment, NOT load, NOT file-specific. Varying crash site
   across identical-admission runs = a genuine defect in the SELF-HOSTED
   compiler's HIR import/re-export chase (src/compiler HIR/module-surface
   layer) — candidates: unbounded recursion in the re-export chase (stack
   exhaustion presents as SIGSEGV and its trip point varies with heap
   layout/traversal order), or a use-after-free in the chase cache.
2. The Rust seed compiles the same tree fine (unit sweep: 0 crashes across
   ~3600 specs), so the fault is either in the Simple compiler sources' HIR
   phase logic or a seed miscompilation that only materializes in the
   stage2-built binary.
3. 3-cycle cap reached (r2/r3/r4). Escalated: this record + user report.
   Next diagnostic step for whoever picks it up: run the stage3 build with
   a C-level stack trace (lldb on the stage2 binary against a reduced
   module graph that reproduces the chase warnings) or instrument the
   chase with a depth guard to distinguish recursion-blowout vs UAF.

Mac bootstrap status: stage2 fully GREEN on unmodified main (first time);
stage3 blocked on the above self-host defect.

## Round 26 (2026-09-19) — correction: recursion ruled out; same defect as the BOOT-20 driver.spl wedge

- Round 25 conclusion 1 named "unbounded recursion in the re-export chase" as
  a candidate. Ruled out on reading the code: the chase is depth-capped at 8
  and carries a visited map, so it cannot recurse unboundedly.
- The Linux aarch64 lane hits the same phase on the same closure
  (`phase3:hir:imports` of `80.driver/driver.spl`) as a spin at ~40GB RSS
  instead of a SEGV. Its 2026-09-18 differential in
  `stage2_native_class_field_text_dict_owner_lost_2026-09-14.md` (BOOT-20)
  shows the Rust seed builds the identical stage3 closure in 380s with the
  same sources, flags and env, so the defect is in the stage2-NATIVE-compiled
  compiler's own execution, not in shared source logic.
- Treat this record as the macOS manifestation of BOOT-20. Rounds 22-25 ran
  on a base that predates BOOT-20 slices 3-5 (#1062, #1071, #1081); any
  re-run must rebuild stage2 on current main first.
- Advantage of this host: the stage2 binary is native aarch64 here, so an
  attached debugger backtrace at the fault is practical (the Linux lane's
  qemu-user gdb stub is 3-10x too slow). That is the next diagnostic.

## Round 27 (2026-09-19) — hypothesis: the macOS SEGV and the Linux 40GB spin are ONE runaway allocation, not two defects

Measured facts, no new run:

| lane | host | fault |
|---|---|---|
| Linux aarch64 (BOOT-20) | qemu-user, large RAM | spins at `phase3:hir:imports` of `80.driver/driver.spl`, 100% userspace CPU, RSS **flat ~40GB** |
| macOS arm64 (this record, r2/r3/r4) | 24GB RAM, ~10GiB free disk | SIGSEGV in `phase3:hir`, 20-40 min in, crash file varies per run |

This host cannot reach the Linux plateau. Physical RAM is 24GB
(`hw.memsize` = 25769803776) and free space on `/System/Volumes/Data` is
~10GiB, which also caps macOS swap growth — a combined backing ceiling near
34GB, just under the ~40GB the Linux lane settles at. A runaway allocation
that plateaus there must instead fail here, and a failed allocation whose
NULL result is stored through presents as SIGSEGV.

This explains the two observations Round 25 could not:

1. **Why the crash file varies across identical-admission runs.** An
   allocation-exhaustion fault lands at whatever allocation happens to cross
   the ceiling, which moves with scheduling order. A use-after-free in a
   depth-capped, visited-map-guarded chase would not wander this freely.
2. **Why the fault is 20-40 min in regardless of `done=` count.** That is a
   time-to-exhaustion signature, not a per-file one.

If this holds, there is no separate macOS HIR defect: the fix is BOOT-20's
stage2-native codegen root cause
(`stage2_native_class_field_text_dict_owner_lost_2026-09-14.md`), and this
record is a second symptom of it on a smaller-memory host.

### Discriminator (cheap, decides it in one run)

Re-run the stage3 replay on a stage2 built from current main while sampling
RSS (e.g. `while :; do ps -o rss= -p <pid>; sleep 10; done`).

- RSS climbs monotonically toward ~30GB and the SEGV lands near the ceiling
  ⇒ same runaway allocation as Linux; close this as a BOOT-20 symptom.
- RSS stays bounded (hundreds of MB to a few GB) and the SEGV still lands
  ⇒ a genuinely distinct macOS fault; then capture `bt` under lldb, which is
  practical here because the binary is native aarch64.

### Blockers on running that discriminator (2026-09-19)

- **No stage2 binary from current main exists on this host.** Every candidate
  found is 2026-09-04..09-08, predating BOOT-20 slices 1-5 (#1059, #1062,
  #1071, #1081). A rebuild is required first.
- **Disk.** `/System/Volumes/Data` has ~10GiB free (98% full) and is falling
  under peer sessions; `src/compiler_rust/target` alone is 11G. A stage2
  rebuild plus stage3 native caches does not fit, and starting one risks
  ENOSPC across peer lanes. Reclaiming space is an owner decision, not this
  lane's.

### Asset check 2026-09-19 13:2x — no admitted post-slice stage2 exists on this host

A peer bootstrap lane (`build/wt-bootstrap-20260919`, base `7a9b584919f`,
which does contain BOOT-20 slices 2-5) built a
`stage3/aarch64-apple-darwin/stage2-runtime-authority/simple` at 12:50 but
then **aborted at stage2**: `VERDICT — ABORTED: stage=stage2 exit=1
signal=none reason=stage2`, `milestone=exit-1`, `main_log=absent`. So the
binary is a runtime-authority artifact from a failed run, not an admitted
stage2, and the discriminator above still needs a stage2 rebuild.

Two consequences:

- Rounds 22-25's "stage2 fully GREEN on unmodified main (first time)" is
  **not confirmed on current main**; a lane on a post-slice base failed
  stage2 today. Whoever owns that lane should report its stage2 error; this
  record only notes that the macOS stage2 green claim is now unverified.
- Disk fell from 12GiB to 7.1GiB free (99% full) during this session under
  peer-lane activity. A stage2 rebuild plus stage3 caches cannot be started
  here without risking ENOSPC across those lanes, so the discriminator is
  deferred on resources, not on method.
