# SPipe Next-Items Plan and Guide — 2026-07-11

Master plan for the eight-item goal pass across active SPipe lanes. Each item maps
to one lane, one owner check, and one evidence command. Statuses below are filled
from live agent verification on current HEAD (not from stale lane logs).

## Item → Lane map

| # | Goal item | SPipe lane | Phase at start | Status |
|---|-----------|------------|----------------|--------|
| 1 | GOT only on baremetal config; hosted SimpleOS launches via filesystem | `simpleos-startup-got-mmap` | verify-done | **PASS (re-confirmed)** |
| 2 | Early file parsing + mmap loading on Linux and SimpleOS | `simpleos-startup-got-mmap` | verify-done | **PASS (re-confirmed)** |
| 3 | Simple web server + simple db server work on SimpleOS (revive if broken) | `simpleos_filesystem_toolchain_servers` | design-done (verify FAIL) | **PASS — web 4/4, DB gate 5/5 (`codex-41`)** |
| 4 | clang-from-FS + simple compiler/loader/interpreter launched from FS | `simpleos_filesystem_toolchain_servers` | design-done (verify FAIL) | clang gate **REVIVED (PASS)**; simple-toolchain payloads blocked on redeploy (diagnosed, sequence documented) |
| 5 | Baremetal + NVMe FW index-based pointers/allocators; update baremetal skill | `nvme_fw_baremetal` (+ skill lib) | dev-done | **PASS — audit clean, skill written** |
| 6 | QEMU WM + host WM rendering hardened, same Simple GUI | `simpleos-qemu-host-gpu-2d` | requirements-done | **PASS** — shared stack confirmed; host checks green; QEMU render+event gate 7/7 |
| 7 | UI CLI interface (T32-style LLM access), common library, wm window list | `ui-cli-llm-access` | design-done | **13/18 checker scenarios PASS**; rest blocked on parallel-session files / redeploy / final review |
| 8 | QEMU vs host WM same-GUI verification with capture (gui/web/2d) | `simpleos-qemu-host-gpu-2d` | requirements-done | **PASS** — WM host+QEMU captures, 2D + web pixel-exact vs oracles (cross-pixel diff = future hardening) |
| 9 | WM hidden daemon mode revived; CLI reaches WM headless; daemon/windowed share code | (extends `ui-cli-llm-access`) | added 2026-07-11 | **DONE** — spec PASS 2/0; CLI wrappers blocked by seed parser bug (filed) |
| 10 | Process-manage gateway + interface on host (simple app) and SimpleOS | (new, reuse existing process APIs) | added 2026-07-11 | **DONE** — host gateway new; SimpleOS ps/kill already existed |

### Item 7: ui-cli-llm-access — compile blockers cleared, 13/18 checker scenarios pass
- Root compile blocker fixed in `access_cli_grammar.spl` (parser rejects dedented multi-line `+`
  continuation — rewrote 3 JSON builders to array-join; added `schema_version` key) and
  `access_cli.spl` (seed-missing `rt_http_url_encode` extern replaced with pure-Simple
  percent-encoder). Lane is co-developed with a parallel session that owns the checker,
  `session.spl`, `handler.spl`.
- Checker: 13/18 scenarios PASS (setup, shared-grammar, t32-compatibility, live-wm-loop,
  identity-ordering-staleness, output-modes, error-taxonomy, environment-states,
  common-ownership, bounded-hot-paths, compatibility-help, live-ui-transport, manual-evidence).
- Remaining 5: live-tui-loop / live-gui-loop / action-safety (parallel-owned UI session/builder
  under seed JIT), performance (needs restored pure-Simple binary — redeploy gate), final
  (requires the AC-10 highest-capability review artifact, produced at integration review).

## Canonical evidence commands

- Item 1/2: `bin/simple run src/app/startup/launch_meta_check.spl -- --simpleos-baremetal|--simpleos-host`;
  `bin/simple test test/02_integration/app/startup_argparse_mmap_perf_spec.spl`
- Item 3: RV64 HTTP smoke wrapper + `check_simpleos_rv64_db_server` (POST /db CREATE/INSERT/SELECT, requires `codex-41` readback)
- Item 4: `scripts/os/ssh_clang_hello_ring3.shs` (clang ELF from FS in ring 3); `scripts/os/simpleos-native-build.shs` (target-native simple toolchain payloads)
- Item 5: allocator/pool audit of `src/lib/nogc_async_mut_noalloc/` + NVMe FW; skill at `.claude/skills/lib/baremetal.md`
- Item 6/8: shared Engine2D path map + capture parity checks (host first, then QEMU wrapper)
- Item 7: `bin/simple test test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl` (17 scenarios) + `scripts/check/check-ui-cli-access.spl`

## Known blockers carried in from lane logs

- Item 3/4: self-hosted compiler lacks `native-build --target` (bug filed
  `doc/08_tracking/bug/self_hosted_simpleos_target_native_build_crash_2026-07-11.md`);
  two stage2 focused specs previously timed out silently; live QEMU PASS claims prohibited until re-proven.
- Item 6/8: lane is requirements-done only — architecture/design phases not yet produced;
  current source proves CPU raster + VirtIO-GPU 2D scanout only.

## Execution model (this pass)

Wave 1 (parallel agents): re-confirm lane 1/2; live-verify web+db smokes; audit clang/toolchain
blocker chain; baremetal allocator audit + skill write; ui-cli-llm-access implementation;
WM rendering-parity audit with captures.
Wave 2 (after reports): fix/revive what Wave 1 proves broken, advance gpu-2d lane to
architecture, integrate, then single highest-capability review of all diffs, state.md updates,
guide finalization.

## Results

### Items 1–2: startup GOT/mmap — PASS (re-confirmed 2026-07-11 on HEAD)
- `launch_meta_check.spl check --simpleos-baremetal /sys/apps/test.smf` → `source=baremetal_got`.
- `launch_meta_check.spl check --simpleos-host <file>` → `source=filesystem|cache=mmap`.
- Policy: `src/app/startup/launch_metadata.spl:116-118` — `baremetal_got` only for
  `target_os=simpleos` + `target_abi=simpleos-baremetal`; all hosted targets (Linux and
  SimpleOS-on-host) use `filesystem`. Kernel launch resolves filesystem bytes before the
  resident table (`src/os/kernel/ipc/syscall_process.spl`).
- `startup_argparse_mmap_perf_spec.spl`: 2 examples, 0 failures (1714 ms).

### Item 3: SimpleOS web + db servers — web PASS, db revival in progress
- Web: `sh scripts/qemu/qemu_rv64_http_test.shs --with-db --expect-http-only` — HTTP
  `/health` and `/` both 200 with correct content types; RV64 QEMU boot + NVFS verified.
- DB: FAILed (Content-Length: -1, `ERR table not found`). Two-layer root cause:
  1. An uncommitted working-tree edit had stripped the hoisted-local workarounds (restored from
     HEAD b060ff7c996) — but rebuild proved this was never the operative breakage in the binary.
  2. REAL blocker: seed LLVM method-arity codegen bug — non-`me` fn class methods called via
     `self.` (`has_table` 2 args / `has_key` 3 args) fail LLVM verification ("Incorrect number of
     arguments"), the build marks the file "non-critical, skipped", and a STALE cached object from
     the old source satisfies the link — so the ELF's DB code was silently old. Tracked:
     `doc/08_tracking/bug/stage4_seed_llvmlib_method_arity_2026-07-06.md`.
  - Side fix: `rt_invlpg` undefined-symbol link blocker (new x86 intrinsic reachable via
    `os/kernel/boot/mmio.spl`) — added riscv64 `sfence.vma` impl in `freestanding_runtime.c`.
  - Revival round 2: `me`-method conversion FIXED the arity blocker (clean-cache rebuild:
    51 compiled / 0 cached / 0 failed — no stale link), HTTP still 4/4, but DB still fails:
    the real terminal blocker is that the seed LLVM backend miscompiles `text.len()` to nil/-1
    in EVERY position on the RV64 freestanding path (hoisting never helped; sibling text methods
    fine; C runtime fns correct — call site never reaches them). Bugs filed:
    `rv64_llvm_nested_len_arg_miscompile_2026-07-11.md`,
    `native_build_noncritical_skip_stale_cache_masking_2026-07-11.md`; minimal repro appended to
    `stage4_seed_llvmlib_method_arity_2026-07-06.md`.
  - FINAL (2026-07-11): seed miscompile ROOT-CAUSED and FIXED — `compile_inline_len`
    (`src/compiler_rust/.../llvm/functions/calls.rs`) inlined `text.len()` recognizing only the
    hosted "STR1" 4-byte magic; freestanding runtimes tag strings with object_type byte 0x01, so
    every freestanding string hit the `-1` phi arm and rt_len was never called. Fix ORs in the
    byte-tag check (hosted-safe; proven by disassembly at all 61 inline-len sites). Gate:
    **5/5 PASS with `codex-41`** (fixed seed, clean cache, 51 compiled/0 cached/0 failed).
    Note: parallel commit 458524b4915 independently moved the DB service to connection-close
    framing (avoids `text.len()`), so the gate also passes without the seed fix; the seed fix is
    proven by disassembly + no-regression and un-breaks `text.len()` for all freestanding RV64.

### Item 5: baremetal + NVMe FW index-based discipline — PASS, skill written
- Evidence: `Handle{index, generation}` pools (`examples/09_embedded/simpleos_nvme_fw/`,
  `fw/fw_pool.spl` 16-slot parallel-array TaskPool), FTL `L2pMap`/`BandAlloc` fixed-slot
  index structures, `riscv_noalloc_pmm.spl` scalar monotonic PMM, NVMe queue wrapping
  u16 SQ/CQ indices; MMIO address math confined to ring-entry offset + doorbells; zero
  growable-alloc hits in baremetal hot paths; one narrow deliberate `unsafe_addr_of` escape
  hatch for DMA physical addresses.
- Skill: `.claude/skills/lib/baremetal.md` (new, 110 lines, matches sibling lib-skill style).

### Item 4: clang-from-FS + simple toolchain from FS — regressed/blocked, Wave-2 running
- clang gate `scripts/os/ssh_clang_hello_ring3.shs`: REGRESSED then **REVIVED (2026-07-11)** —
  gate exits 0: `hello from clang on simpleos` + `[user] exit rc=42`,
  serial `spawn:preloaded len=13888`. Two compounding root causes fixed (+32 lines, pure Simple):
  1. Streaming rewrite dropped the boot-preload short-circuit while exec-time FAT/NVMe reads
     return 0 in the merged SSH kernel (tracked: `x64_ssh_kernel_fat32_stream_open_zero`);
     preload short-circuit reinstated at `x86_64_fs_exec_spawn.spl:78`, streaming kept as fallback.
  2. `mmio_disable_test_mode()` was imported/called but never defined — linked as a weak no-op
     stub under `SIMPLE_ALLOW_FREESTANDING_STUBS=1`, and since freestanding builds skip
     module-level initializers, `_mmio_test_mode` read garbage-true from un-zeroed .bss, making
     every `mmio_read*` (incl. ELF-magic checks) return nil. Defined at `mmio.spl:118`.
  Streaming-from-FS remains blocked on the exec-time device-clobber bug (separate fix lane).
- Toolchain rebuild diagnosis (2026-07-11, definitive — see
  `doc/08_tracking/bug/self_hosted_simpleos_target_native_build_crash_2026-07-11.md`):
  THREE distinct failures, none previously conflated correctly:
  1. `release/.../simple` (Jul 7): stale 2-arg `rt_env_set` runtime vs 4-arg callers (landed
     5e36474fde0 Jul 10) → strlen segfault on any native-build. Fix = rebuild+redeploy.
  2. `--backend=llvm-lib` on today's stage3: deterministic SIGSEGV in LLVM
     `DataLayout::setAlignment` via inkwell `Module::set_data_layout`
     (`backend_core.rs:846`) — even hello-world; llc never reached (not #131/#133). Bisect lane.
  3. Bootstrap pipeline masks stage failure with overall exit 0 (recorded in masking bug).
  Viable rebuild paths found: stage3 `--backend=cranelift` (CAVEAT: full-src/app output was
  26 KB / "1 compiled" — must verify not stub-collapsed before trusting) and Rust seed
  `SIMPLE_BOOTSTRAP=1 --backend=llvm` external-llc (memory-documented real redeploy path).
  Redeploy sequence documented in the bug file; EXECUTION DEFERRED until in-flight agents
  finish (mid-session binary swap previously confounded verification — #141 lesson).
- simple toolchain payloads (AC-5/6): blocked exactly as logged — no binary is both non-seed and
  `--target`-capable (`release/.../simple` from Jul 7 lacks `--target`; the Jul 11 `bin/simple`
  has it but self-identifies as Rust bootstrap seed). Self-hosted rebuild core-dumps pre-output;
  secondary blocker: `rt_enum_new` ABI mismatch (Rust registry `[I32,I32,I64]` vs LLVM-widened
  `(i64,i64,i64)`) failing `simple_core` archive on `core_string.spl`. Diagnosis agent running;
  target-triple plumbing (`x86_64-unknown-simpleos`) exists in 3 compiler files but is unexercised.

### Items 6/8: WM rendering parity — shared stack confirmed; host checks regressed
- Shared stack: host WM (`src/os/compositor/host_compositor_entry.spl` + `compositor_engine2d.spl`)
  and SimpleOS/QEMU WM (`src/os/desktop/shell.spl` + `engine2d_baremetal_core.spl`) both use the
  same `Engine2D` core and shared `common.ui.window_scene*` chrome/scene code; only the pixel-sink
  backend adapters differ (hosted SDL2/Cocoa/Win32 vs baremetal framebuffer/VirtIO-GPU), as designed.
- QEMU capture: `check-simpleos-x86-64-wm-render-event-evidence.shs` render gate PASS today —
  real QMP screendump `build/os/wm_x86_64_screendump.ppm` (1024x768, wallpaper color verified at
  7 anchors). Event gate FAIL: garbage 64-bit `count=` serial markers (serialization bug).
- Host regressions RESOLVED (Wave-2, 2026-07-11): the "segfault" premise was stale —
  `check-shared-wm-renderer-unification-evidence.shs` failed on a stale grep source-contract
  (F7) after the motion-background commits added `t_micros` to the render funnel; pattern fixed
  at `check-shared-wm-renderer-unification-evidence.shs:157`, check PASSES (logic 4/0).
  `check-hosted-wm-capture-evidence.shs` PASSES (cold-cache first run ~60s vs 45s timeout was
  the earlier failure; warm ~9s).
- Event gate: garbage `count=` root-caused to TWO native-dynload compiler bugs — module-level
  `var = 0` static initializers dropped (counters started as `.text` bytes) and u64-global
  interpolation boxing to nil. Workarounds in `wm_entry.spl` (runtime-restore initializers in
  `spl_start()`, interpolate typed locals); bug filed:
  `native_dynload_module_var_static_init_dropped_2026-07-11.md`. Also fixed keyboard drain
  stealing PS/2 AUX bytes. Event gate now **7/7 PASS, overall RESULT: PASS** — the mouse gap was
  a third facet of the dynload boxing bug: module-global reads arrive boxed in comparison
  context, so `if <global> == 1:` was FALSE despite memory holding 1 (proven via QMP `pmemsave`),
  dead-coding the PS/2 mouse poll + minimize tick. Fixed with `!= 0` gates and local hoisting in
  `wm_entry.spl`. Known residual (documented in the bug file): marker x/y print a stable masked
  box value, and unboxing is operator-dependent (`+` unboxes, `&` doesn't) — compiler lane.
- Remaining gap even when green: no harness cross-compares host vs QEMU pixels (each compares
  against its own CPU oracle) — a direct PPM diff step is the planned hardening addition.
- Item 8 capture evidence (2026-07-11, all host checks on current binaries):
  - Simple 2D: `check-cpu-simd-engine2d-evidence.shs` PASS — SIMD-kernel diagram checksum
    `79321896458941` == scalar-oracle checksum, all sub-op mismatches 0, policy
    exact-bitmap-no-blur-no-tolerance. Report `doc/09_report/cpu_simd_engine2d_evidence_2026-07-11.md`.
  - Simple Web: `check-simple-web-engine2d-js-bitmap-evidence.shs` PASS — native ARGB checksum
    `26296152649728` == Node/JS baseline, mismatch_count=0, no tolerance; 6µs/frame vs 90µs JS.
    Report `doc/09_report/simple_web_engine2d_js_bitmap_evidence_2026-07-11.md`.
  - Simple GUI/WM: host PPM capture + QEMU QMP screendump both PASS (see above).
  - Residuals: 2D check is kernel-layer (no full-scene PPM); web check is one scene/one JS
    runtime; host↔QEMU cross-pixel diff still to be added in the gpu-2d lane.

### Items 9/10: WM daemon mode + process-manage gateway — research done, design fixed
Research ground truth (2026-07-11):
- No prior WM-daemon plan/implementation exists in docs or git history. Three current
  "headless" mechanisms, none resident: (a) `simple play` WM CLI shells out per-call to
  xdotool/osascript/PowerShell (`src/lib/nogc_sync_mut/play/wm/mod.spl`) — nothing to attach to
  when no OS WM runs; (b) `HeadlessHostCompositorBackend`
  (`src/os/compositor/host_compositor_entry.spl:53-126`) — library class used only by an
  evidence spec; (c) `run_headless_with_access_store` (`src/app/ui.none/app.spl:115`) — one-shot
  batch render to the persisted access store.
- Breakage observed: interpreted `bin/simple run src/app/ui/main.spl -- gui ...` exceeds the
  800-module interpreter cap; compiled `bin/simple ui gui ...` hangs with no readiness signal —
  no channel a CLI could poll.
- Reusable assets: host `daemon_sdk` (`src/lib/nogc_sync_mut/daemon_sdk/{client,types}.spl` —
  ensure_running/submit/poll/stop protocol, proven by the test-runner daemon); host process APIs
  (`src/lib/nogc_sync_mut/io/process_ops.spl`, `process_set/manager.spl` — no list-all, no
  `simple process` CLI yet); SimpleOS process table (`pt_ext_register/lookup/set_state/reap/
  count/list_pids` in `src/os/kernel/scheduler/process_table_extended.spl`; shell has no ps/kill).

Design (minimal, shared-code):
- I9-daemon: add a resident WM daemon entry (`simple wm daemon`, hidden window = headless
  compositor backend) that reuses the SAME `SharedWmScene`/Engine2D compositor code as windowed
  mode — only the pixel-sink backend and the visibility flag differ. Expose the daemon_sdk
  channel; register windows in the same access store the UI CLI reads.
- I9-cli: `wm windows list` (and the ui-cli-llm-access loop) routes: live daemon channel if
  running → OS-window shell adapter fallback → read-only store; headless never fabricates.
- I10-host: `simple process list|spawn|kill|wait` gateway command over daemon_sdk wrapping
  process_ops/ProcessManager, sharing the `AccessCommandDescriptor` grammar from
  `access_cli_grammar.spl` for output/error shape.
- I10-simpleos: shell `ps`/`kill` builtins over `pt_ext_*` plus the same command grammar via the
  existing boot HTTP/service channel, so host and guest expose one process-gateway interface.
- Order: I10-simpleos (cheap, independent) → I10-host → I9 (needs ui-cli lane merged; the
  compiled-ui hang and module-cap are tracked blockers for full GUI daemon; headless-backend
  daemon does not hit them).

Implementation result (2026-07-11, committed 9feb36cb72a2):
- I10-simpleos: premise stale — shell `ps`/`kill` already exist (`commands_fs.spl:369,395`,
  syscalls 5/6/7 reading the live scheduler, richer than `pt_ext_*`); nothing added.
- I10-host: `simple process list|spawn|kill|wait` (`src/app/process/{main,registry}.spl`,
  dispatch `table.spl:680`); SDN registry `~/.simple/cache/process_gateway.sdn`; `--json`;
  shared AccessResult/AccessError shapes. List covers gateway-managed processes (no /proc).
- I9: `src/app/play/wm_daemon.spl` — resident headless WM via `init_host_wm(Headless)`, same
  compositor code as windowed; daemon_sdk file-IPC (serve/start/windows-list/window-open/
  window-close/status/stop) + `wm_daemon_client.spl`; `wm windows list` tries daemon first.
- Evidence: `wm_process_gateway_spec.spl` PASS 2/0 (real sleep-5 spawn/kill/wait; daemon
  open→list(1, Terminal)→stop). Untested: CLI wrappers under the seed (parser dedent bug on
  `access_cli_grammar.spl`, filed `seed_parse_access_cli_grammar_dedent_2026-07-11.md` —
  also blocks the pre-existing `simple play windows`); daemon serve loop over real IPC;
  SimpleOS builtins at runtime.
- Interpreter finding (for future lanes): in-place mutations through TYPED class params are
  lost when the frame returns (dynamic params persist; module-scope scalars persist, class
  vars don't) — pattern: return-the-object. And sspec `expect(a == b)` desugars to
  `.to_equal(b)` — bind comparisons to a `val` first.

## Operator guide (canonical commands after this pass)

- Startup policy probe: `bin/simple run src/app/startup/launch_meta_check.spl check
  --simpleos-host <file>` (expect `source=filesystem|cache=mmap`) / `--simpleos-baremetal`
  (expect `source=baremetal_got`).
- Servers live gate: `sh scripts/qemu/qemu_rv64_http_test.shs --with-db --expect-http-only`
  (5/5 incl. `codex-41`; add `--allow-prebuilt-artifact` while the deployed binary is a seed).
- clang-from-FS ring-3 gate: `sh scripts/os/ssh_clang_hello_ring3.shs`.
- WM parity: `sh scripts/check/check-shared-wm-renderer-unification-evidence.shs`,
  `check-hosted-wm-capture-evidence.shs` (warm run), and QEMU
  `check-simpleos-x86-64-wm-render-event-evidence.shs` (render + 7/7 events).
- 2D/web pixel parity: `check-cpu-simd-engine2d-evidence.shs`,
  `check-simple-web-engine2d-js-bitmap-evidence.shs`.
- UI CLI access: `bin/simple run scripts/check/check-ui-cli-access.spl --scenario <name>`.
- Process gateway: `bin/simple process list|spawn|kill|wait [--json]`.
- WM daemon: `simple play daemon start|windows-list|window-open|window-close|status|stop`
  (backing modules spec-proven; CLI wrapper pending the seed parser bug fix).
- Redeploy wall (next lane): follow the sequence in
  `doc/08_tracking/bug/self_hosted_simpleos_target_native_build_crash_2026-07-11.md` —
  cranelift output must be proven non-stub-collapsed; the seed external-llc path is the
  memory-documented real route (llc blockers #131/#133 apply to full-app scope).
