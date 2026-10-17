# SMUX Windows verification checkpoint

Host: Windows 11 Pro 10.0.26300 x64, native PowerShell. Source base:
`release_phase3`, `a1d66e522066c97045255f6c603058fca461f0f1`; working branch
`work/smux-windows-phase3-20261016` in `D:/dev/simple-smux-phase3`.

**STATUS: TEST_BLOCKED. Major tmux parity: FAIL. Goal remains incomplete.**

Latest actual build result: the reviewed immutable compiler campaign terminated
at Stage 2 linking after compiling 1349 modules. `__simple_pow` is unresolved
from `mir_fold_binop`; no final Stage 2 compiler, Hello/admission, smux binary,
or Phase 3 result exists for this campaign. The objects and failed link log are
preserved. See
`doc/08_tracking/bug/windows_stage2_pow_runtime_owner_missing_2026-10-16.md`.
Investigation targets the actual runtime composition. No unchanged full-build
retry or Rust seed application fallback has been performed.

## Current continuation checkpoint

The branch now also contains an independent foreground owner with bounded
authenticated TCP requests, disposable compiled client modes, continuous
output polling, persisted production named layouts/rectangles, cell-preserving
composite capture and centralized command exit-status handling. Astra accepted
source and authored-manual quality, including Unicode edge tests and real
external-process scenario designs. No runtime pass follows from that review.

Additional authored coverage now includes bounded input queues, portable UTF-8
prefix handling, retained VT scrollback, native provider selection and codecs,
and child-observed resize. All remain unexecuted. Existing geometry unit
coverage also changed; its manual is an authored draft. Paths and traceability are consolidated in
`doc/03_plan/sys_test/smux_windows_phase3_features.md`. Generated manuals,
zero-stub receipts and maintenance scans remain pending.

The later Phase 2 diagnostic used producer `06ccfabd...`. Retained artifacts
establish 46 native object files and a concrete LLVM failure in
`smux_pane_spawn_pty`: unsupported transfer-envelope lowering. MIR treated
resolved synchronous `std.sys.pty.spawn` as a thread spawn by bare name. A
semantic owner-based compiler repair is authored with regressions and an
actual imported-call fixture; it is fixed in source only. Neither inspected
compiler contains the patch. The frozen build predates the later owner/layout
code and cannot validate those new features.

Native Winsock/ConPTY owners and ordered source overlays are now authored.
Astra found and reviewed source fixes for TCP lifetime connection exhaustion
and PTY cleanup falsely certifying unreleased resources; no runtime acceptance
follows. Native queues retain overlapped writes, real resize precedes service
commit, and finite shutdown checks deferred cleanup. Scrollback is implemented
in the production VT and exposed through the focused-pane history command.

The immutable rebuilt-compiler campaign includes the MIR fix. Its Rust seed
build completed successfully in 20m34s and native-all completed in 13m27s.
The same campaign reached actual Stage 2 native construction, with over 900
retained objects and a CPU-active builder. This is bootstrap progress, not a Phase 2 product
or general test result. Current product edits are outside that frozen compiler
snapshot and require a separate frozen product build with the selected overlays.

Remaining gates include a rebuilt/matching admitted producer, Phase 2 and
Phase 3 product execution, general SSpec/core/MCP smoke, executed Windows
provider fixtures under outer watchdogs, owner fairness under input backpressure,
independent interactive screens, owner console/job-detach semantics, actual
child resize, and interactive copy/key-binding behavior. No merge or release
is admitted. PR 3508 remains an unfinished draft against `release_phase3`.

The interactive continuation adds the same hosted binary's `--attach` mode,
explicit per-client window/pane targets, safe styled/cursor frames, default
Ctrl-B commands, incremental copy navigation and line-selection clipboard
actions. A Win64 console capability saves/restores both console modes and uses
bounded event reads. The native fixture launches two actual attach clients
inside distinct ConPTYs; both producer runs remain pending. Astra identified
batched-copy-key, differing-client-size and bottom-right-wrap defects during
source review; fixes and regression scenarios are being reviewed. This source
work does not close any runtime or full tmux parity gate.

Final source-freeze review: Astra accepted the corrections for copy-key
batching, bottom-right scrolling, differing client dimensions, split/frame
interleaving and dense history replies. All demonstrated P1 findings from that
bounded review are resolved in source. Native execution, selected user32 link,
two-client behavior and mode restoration remain unverified. The source guard,
patch formatting and executable-spec layout checks are static evidence only.

The earlier checkpoint evidence below is retained as history. The build report
contains corrected object/ICE evidence beyond the outer timeout logs.

The scoped implementation corrects directional split geometry, refuses
nonpositive resize dimensions, and makes client admission/refusal and rebind
match the actual four-client registry. Astra independently reviewed these
changes and accepted the source and authored manual quality by inspection.
That acceptance is not execution or release qualification.

| Criterion | Current evidence | Result |
|---|---|---|
| Separate sessions/windows and ownership | 15 new direct production-service SSpec scenarios cover these and the bounded API corrections | Authored; not executed |
| Windows child execution, two panes, same-process detach/reattach | 3 new ConPTY scenarios use child-expanded output tokens and explicit Windows host checks | Authored; not executed |
| Compile with Phase 2, then Phase 3 | Exact producer identities, diagnostic commands and outcomes retained in `smux_windows_build_2026-10-16.md` | No qualified successful build |
| Modern manuals and maintenance | Both authored manual mirrors explicitly mark generation pending | Docgen/zero-stub/maintenance gates blocked |
| Runtime environment facade boundaries | Working and staged direct-env-runtime guards both returned `STATUS: PASS` | PASS |
| Executable spec layout | `rg --files doc/06_spec -g '*_spec.spl'` counted zero | PASS |
| Patch formatting | Scoped `git diff --check` returned zero | PASS |
| Full tmux feature parity | Independent audit identifies missing persistent owner/reconnect, unattended draining, live resize and other interaction gaps | FAIL |
| Merge/release readiness | No executed SSpec evidence or qualified build; no verification PASS | Not ready; no merge or release |

The SSpec plan is `doc/03_plan/sys_test/smux_windows_phase3_features.md`.
The independent source audit is `smux_windows_tmux_audit_2026-10-16.md`.
Windows operating and qualification guidance is
`doc/07_guide/tooling/smux_windows_verification.md`.

The original shared checkout and concurrent bootstrap sessions were preserved.
Existing unrelated image/asset modifications are outside this lane and must
not enter its commit. No Rust seed was used as a product-build fallback.

Continue with an exact, matching admitted producer and real Windows build/test
results. Do not reinterpret metadata attachment tests as independent screens,
active capture polling as an unattended daemon, or source review as a runtime
pass. The original full feature scope remains outstanding.

## Final frozen-source diagnostic result

**TIMEOUT_120S; no smux executable.** Native PID 22392 reached the explicit 120-second diagnostic limit. Its process tree was terminated successfully (owned children 4324 and 796); a subsequent process query found neither parent nor direct children alive. This was a diagnostic timeout, not an admitted compiler FAIL/PASS receipt.

The fresh immutable source snapshot passed the previous admission boundary: source closure completed with 57 modules, load_sources reported 109 files, parsing advanced, and HIR completed 57/57 modules with zero failed modules. The compiler journal reported approximately 20.8 seconds through HIR; the total process lifetime reached 120 seconds. At 90 seconds the parent had 85.125 CPU seconds and 1,701,662,720 bytes RSS; at termination its RSS was 1,702,252,544 bytes. No code-generation/link completion was observed. Stderr retained unresolved declaration/re-export diagnostics involving `Option` and `Result` in `lib.nogc_async_mut.env.variables`, `lib.nogc_async_mut.env.platform`, and `lib.nogc_sync_mut.env.types`. These are unresolved-origin warnings; this interrupted run does not prove the later terminal type error.

The compiler HIR log reported 0 hits, 57 misses, 57 stores, 0 I/O failures. HIR storage resolved to the frozen-source-specific project namespace `/tmp/simple-cache/v1/projects/7dcf7beb22f33342151bfd60494ef3d85d51da9a92b6318d2576edd1a65e5941/native-build/v1/default/hir`; the explicit frontend queue remained under the requested `phase2-frozen/cache/default/frontend/queue-22392-0`. The producer's general cache flag therefore does not place every HIR artifact under its argument; the unique frozen project identity separates this run from other source owners.

Full evidence: `build/smux-windows/phase2-frozen/build.stdout.log`, `build/smux-windows/phase2-frozen/build.stderr.log`, `build/smux-windows/phase2-frozen/build.exit.txt`, `build/smux-windows/phase2-frozen/timeout-kill.log`. The prior two attempts remain retained. No further identical retry was performed. Phase 3 compilation and general SSpec execution remain BLOCKED by unavailable qualified producers.

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
