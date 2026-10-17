# smux Windows Phase 2 / Phase 3 evidence

Scope: current Windows host, release_phase3 source checkout at `D:/dev/simple-smux-phase3`, revision `a1d66e522066c97045255f6c603058fca461f0f1`.

Host: Microsoft Windows 11 Pro, version 10.0.26300, 64-bit. This is native Windows execution, not WSL evidence.

## Producer identity

- Located Phase 2 compiler: `D:/dev/simple-phase3/.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe` (22,849,536 bytes).
- Exact observed and frozen SHA-256: `2700c805ea6ea61b2430a73b13fa3fba4ea45cddf6a33d38a7e019cb18cd08ac`.
- Frozen diagnostic copy: `build/smux-windows/phase2/compiler/simple.exe` relative to the repository root.
- Adjacent `stage2-provenance.receipt` and `stage2-sanity.receipt` instead bind `5ba802e78d60fe7447d212e982a6ade366e9705c290b79e297c9b14cfba3c649`. The referenced current `stage2-admitted/admission.env` is missing; the archived admission binds that older candidate. Current compiler admission is therefore INVALID. No receipt was altered.
- `native-build --help` executed and printed its compiler usage and source/entry/backend/output options. The exact output is retained in `build/smux-windows/phase2/help.stdout.log` and `build/smux-windows/phase2/help.stderr.log`. This proves command availability, not compiler admission or a working SSpec runner.
- No canonical Phase 3 or Phase 4 `simple.exe` was found across the local `D:/dev/simple*` bootstrap roots inspected. Phase 3 smux compilation is BLOCKED pending its producer.
- Separate ongoing bootstrap at observation time: native PID 8984, executable `D:/dev/simple-p3sync/.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe`. Its existence does not prove a finished Phase 2/3 compiler. Other-session process and caches were preserved.

## Actual diagnostic compile

This unadmitted diagnostic is explicitly distinguished from an admitted build. No Rust seed fallback was used.

Working directory: `D:/dev/simple-smux-phase3`.

```powershell
& build/smux-windows/phase2/compiler/simple.exe native-build --source src/os --source src/lib --source src/app/hosted_apps --entry-closure --entry src/app/hosted_apps/smux_client.spl --backend=llvm --cache-dir D:/dev/simple-smux-phase3/build/smux-windows/phase2/cache --output D:/dev/simple-smux-phase3/build/smux-windows/phase2/smux.exe
```

The first actual build refused with `SCV-E-ADMISSION: compile-event-journal-missing (first build in this checkout: rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)`. Logs: `build/smux-windows/phase2/build.stdout.log`, `build/smux-windows/phase2/build.stderr.log`.

A single changed-input retry sets `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, as requested by that diagnostic, retaining the same isolated output/cache. Logs: `build/smux-windows/phase2/build-cold.stdout.log`, `build/smux-windows/phase2/build-cold.stderr.log`; terminal code is retained in `build/smux-windows/phase2/build-cold.exit.txt`: **exit 1**. Native PID 2180 reached terminal state. The refusal was `SCV-E-ADMISSION: snapshot-index-drift:src/os/apps/smux/layout.spl`. No `smux.exe` was produced. CPU and RSS progressed during the attempt (50.8 CPU seconds and approximately 1.06 GB RSS at one observation); this was not an indefinitely idle parent. The source-snapshot admission refusal does not establish a parser, type checker, code generator, or linker outcome. A later attempt needs a frozen source snapshot after ongoing source changes finish.

Build scope is the hosted smux client entry actually used by `bin/smux.cmd`; its implementation imports `os.apps.smux.smux_remote.smux_remote_main`. Native build evidence alone would not demonstrate persistent daemon, interactive pane rendering, ConPTY operation, multiple attached terminals, or positive SSpec assertions; those need separate runtime checks.

## Frozen-source follow-up

A third diagnostic is being prepared from a detached local checkout at D:/dev/simple-smux-build-frozen-20261016, copying the final api.spl and layout.spl changes into a committed snapshot. No SSpec or docgen is executed on the compiler-only Phase 2 tool. Prior attempts and logs are retained.


Third diagnostic source: detached frozen checkout `D:/dev/simple-smux-build-frozen-20261016`, local snapshot commit `df932d258f65abcdb45fd0f94435fbf3b1519e8e`. It includes release_phase3 plus the final two source edits. `api.spl` SHA-256 is `bbd4339447d274d1ba88cc92d81657ef522014aafd93eebc848890ad95d300a2`; `layout.spl` SHA-256 is `fd2808363e921b882eed506d84541e35a7ccc567f5da11e344f7b0ce1f954998`.

The third command uses the same frozen Phase 2 compiler and arguments as above, except working directory is the frozen checkout, cache is `D:/dev/simple-smux-phase3/build/smux-windows/phase2-frozen/cache`, output is `D:/dev/simple-smux-phase3/build/smux-windows/phase2-frozen/smux.exe`, and `SIMPLE_SCV_INVENTORY_COLD_INIT=1`. Exact operands are retained in `build/smux-windows/phase2-frozen/build.args.txt`. Native PID 22392 was started, with a 120-second monitored process-tree limit. Logs are `build/smux-windows/phase2-frozen/build.stdout.log` and `build.stderr.log`; terminal result will be recorded in `build.exit.txt`. No admission checks were disabled, and the compiler remains unadmitted.

## Final frozen-source diagnostic result

**TIMEOUT_120S; no smux executable.** Native PID 22392 reached the explicit 120-second diagnostic limit. Its process tree was terminated successfully (owned children 4324 and 796); a subsequent process query found neither parent nor direct children alive. This was a diagnostic timeout, not an admitted compiler FAIL/PASS receipt.

The fresh immutable source snapshot passed the previous admission boundary: source closure completed with 57 modules, load_sources reported 109 files, parsing advanced, and HIR completed 57/57 modules with zero failed modules. The compiler journal reported approximately 20.8 seconds through HIR; the total process lifetime reached 120 seconds. At 90 seconds the parent had 85.125 CPU seconds and 1,701,662,720 bytes RSS; at termination its RSS was 1,702,252,544 bytes. No code-generation/link completion was observed. Stderr retained unresolved declaration/re-export diagnostics involving `Option` and `Result` in `lib.nogc_async_mut.env.variables`, `lib.nogc_async_mut.env.platform`, and `lib.nogc_sync_mut.env.types`. These are unresolved-origin warnings; this interrupted run does not prove the later terminal type error.

The compiler HIR log reported 0 hits, 57 misses, 57 stores, 0 I/O failures. HIR storage resolved to the frozen-source-specific project namespace `/tmp/simple-cache/v1/projects/7dcf7beb22f33342151bfd60494ef3d85d51da9a92b6318d2576edd1a65e5941/native-build/v1/default/hir`; the explicit frontend queue remained under the requested `phase2-frozen/cache/default/frontend/queue-22392-0`. The producer's general cache flag therefore does not place every HIR artifact under its argument; the unique frozen project identity separates this run from other source owners.

Full evidence: `build/smux-windows/phase2-frozen/build.stdout.log`, `build/smux-windows/phase2-frozen/build.stderr.log`, `build/smux-windows/phase2-frozen/build.exit.txt`, `build/smux-windows/phase2-frozen/timeout-kill.log`. The prior two attempts remain retained. No further identical retry was performed. Phase 3 compilation and general SSpec execution remain BLOCKED by unavailable qualified producers.

## New Phase 2 producer follow-up

A materially new p3sync Phase 2 candidate appeared: `D:/dev/simple-p3sync/.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe`, 22,904,832 bytes, SHA-256 `06ccfabd9aaed34fdf7bda5e4b170ee28678a0549fa9bb5dc3b995eb522e855c`. It was copied immutably into `build/smux-windows/phase2-p3sync-06ccfabd/compiler/simple.exe`, and its copied hash matched. No adjacent provenance/sanity receipt or current `stage2-admitted/admission.env` existed at launch; it remains explicitly unadmitted. Other-session qualification was still running and was preserved.

The actual focused smux native-build command is the previously recorded three-source-root command, now using that frozen compiler, `build/smux-windows/phase2-p3sync-06ccfabd/cache`, and output `build/smux-windows/phase2-p3sync-06ccfabd/smux.exe`. Working directory remains frozen commit `df932d258f65abcdb45fd0f94435fbf3b1519e8e` in `D:/dev/simple-smux-build-frozen-20261016`; `SIMPLE_SCV_INVENTORY_COLD_INIT=1`. Exact operands and stdout/stderr are retained under the new row. Native PID 2728 started with a monitored 240-second process-tree limit. This is a new-producer diagnostic, not another identical attempt with the previous producer. General SSpec and docgen were not executed. Result pending.

### New producer terminal result: TIMEOUT_240S

The new `06ccfabd...` Phase 2 diagnostic reached its 240-second monitored limit without producing `smux.exe`. Owned parent PID 2728, worker 14100, and console child 14568 were terminated successfully; a subsequent independent process query found none alive. The native-build source closure and HIR completed 57/57 modules, zero failed, HIR journal elapsed 18.264 seconds. HIR cache correctly invalidated all 57 old-producer headers and stored 57 new entries. The parent waited on the actual native-build worker: worker CPU advanced from 29.36 to 72.16 seconds in separate observations, so parent idleness did not imply absent work. Parent RSS reached 2,427,871,232 bytes; worker RSS was approximately 882 MB at one observation. No codegen/link completion was observed; unresolved `Option`/`Result` origin/re-export warnings remained in stderr and are not classified as a completed terminal type error.

Retained evidence directory: `build/smux-windows/phase2-p3sync-06ccfabd/` (`build.args.txt`, `build.stdout.log`, `build.stderr.log`, `build.exit.txt` = `TIMEOUT_240S`, `timeout-kill.log`, frozen `compiler/simple.exe`, private frontend `cache`). The compiler's HIR cache uses the previously documented frozen-source project namespace under `/tmp/simple-cache`, with producer-sensitive header invalidation observed.

At the terminal observation, the original p3sync Stage 2 adjacent provenance and sanity receipts, current `stage2-admitted/admission.env`, and Phase 3 `simple.exe` were all absent. No p3sync `simple.exe` process remained live at that observation. This does not prove its enclosing bootstrap session completed successfully; it establishes that there was no runnable admitted Phase 2/Phase 3 producer available to this lane at that time. No repeated same-producer build or SSpec execution followed. The goal remains incomplete.

### Retained-artifact diagnosis: actual LLVM codegen failure

A follow-up inspection of retained artifacts, without rerunning the compiler, materially narrows the result. The previous log-only phrase “no codegen/link completion was observed” must not be read as no code generation: the private cache scope `cache/scbfef51681219ad424122cf7010ebac1/phase.marker` says `frontend-done, codegen-started`. The output directory contains **46 real `.o` files totaling 1,008,700 bytes and 46 capsule receipts**. All 46 output paths named by `cache/build_cache.sdn` exist. The last object was `lib.common.cache_path_policy_v1`, 18,879 bytes, written at 09:28:38.392. There is no executable/link completion.

More decisively, `build/smux-windows/phase2-p3sync-06ccfabd/simple-aot-diagnostic-bd476e2b8a1e45800b9a09804547566d/message` retains a 307-byte backend failure, written 09:28:08.126:

> compile error: LLVM runtime transfer-envelope lowering is not implemented [module=os.apps.smux.api function=os.apps.smux.api.smux_pane_spawn_pty at=:0:0]

The message occurs twice in that file. The independent ICE receipt `retained-ice/ice_receipt.14100.part` records `kind=caught`, `phase=codegen`, `module=os.apps.smux.api`, `backend=llvm`, and the same failure. Its sibling breadcrumb journal contains 47 codegen start/done pairs, including the API failure, then completes the last `cache_path_policy_v1` unit. Thus API codegen failed before timeout while independent codegen continued; the later process timeout also prevented the collected failure from reaching the final command result. The 11 source modules without cached object entries include this API plus ten export/extern/trait facade modules; absent entries alone do not mean eleven compile failures.

The warned `env/variables.spl` and `env/platform.spl` actually emitted objects of 22,674 and 36,256 bytes. Their `Option`/`Result` origin warnings therefore did not prevent those modules from producing native code. `std.sys.pty` also emitted a 3,023-byte object; this does not prove its external runtime PTY operations work. The hosted client closure has no socket/TCP module, so Windows TCP stubs cannot explain this specific compilation failure. This build covers the frozen initial hosted-client source; it does not build subsequent server/layout feature additions in the editing checkout.

A source-based root-cause inference is now available. `smux/api.spl` imports `std.sys.pty.spawn as pty_spawn` and the failed function calls `pty_spawn(handle, command_line)`. MIR direct-call lowering currently decides `is_thread_boundary` from the bare name `spawn`/`spawn_actor` (release source `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:6830`, p3sync source line 6872), then emits `TransferOut` for each argument. The LLVM owner explicitly rejects that instruction (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, p3sync line 1182). The likely compiler bug is treating an ordinary owner-qualified PTY launch as a thread/actor transfer because its origin function is named `spawn`. Confirm by inspecting that call's MIR in a focused regression, then classify transfer semantics by the resolved owner/symbol; preserve true actor/thread transfers. No source workaround or compiler edit was made by this build lane.

An unchanged cached continuation is not justified: source-qualified reuse of the 46 retained capsule/object pairs is supported, but cannot fix the deterministic unsupported instruction in the missing API object. A next compilation needs a reviewed producer fix or a focused MIR diagnostic, rather than another longer timeout. No continuation or rerun was launched.
