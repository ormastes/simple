# Two-domain-tree rt_* ratchet tranche (2026-11-27)

Owner: ratchet owner (lane `work/p3-sweep-20261127`, P3 sweep of
`doc/08_tracking/bug/rt_call_site_ratchet_regression_2026-09-05.md`).
Reason: adjudicate the non-allowlisted `rt_*` call sites in the two stdlib
domain trees named by that bug — `src/lib/nogc_sync_mut` and
`src/lib/nogc_async_mut_noalloc` — against the same mechanical criterion the
2026-08-28 residual-scope adjudication (`provider_classification_2026-08-28.md`)
and the 2026-11-07 baremetal HAL adjudication
(`noalloc_baremetal_hal_providers_2026-11-07.md`) applied.

## Measured state (before this tranche)

Gate: `sh scripts/check/check-no-direct-rt.shs --roots src`
(config/check/must_check_gates.sdn row `no-direct-rt`, bootstrap/automated).

- Working tree: forbidden=6926, baseline=6290 → FAIL (+636).
- Committed HEAD (`--rev HEAD --count-only`): forbidden=6926 — identical, so
  the overage is committed content, not concurrent worktree edits.
- Two-tree offenders: 156 files / 980 forbidden sites
  (nogc_sync_mut 143 files / 926 sites; noalloc 13 files / 54 sites),
  captured per-file in the lane cache (`--offenders` output).

The tracked baseline `scripts/check/no_direct_rt_baseline.txt` was NOT modified
in this tranche (per the bug doc: the baseline is not to be regenerated to
paper over growth). The ratchet now holds at 6290 with ~60 sites of headroom.

## Admission criterion (mechanical, per existing precedent)

A file was admitted to the allowlist only if its header/role shows it is:

- (a) an already-typed 1:1 wrapper module outside `ffi/`/`sffi/` by filename
  only — declares its `rt_*` externs once and wraps each in typed fns
  (same shape as the existing `io/*_ops.spl` / `atomic.spl` entries); or
- (b) a hardware / driver / vendor-library ABI with no deeper Simple layer
  (same class as vulkan/metal/SDL/winit/font/SIMD entries); or
- (c) a native-authoritative owner leaf (SOSIX / Windows-private /
  Linux-process / container-observation families, same class as
  `dir_entry_ops.spl` / `dma.spl` / `sosix/secure_temp_dir.spl`); or
- (d) a runtime seam with no deeper Simple layer beneath it (SPipe BDD result
  recording, coverage, fork-test primitives, DAP debug hooks, profiler,
  signal stubs, platform entropy, math/random SFFI, refcount surface named by
  `doc/05_design/compiler/memory/build_session_memory_model_v1.md` §4); or
- (e) a forced no-alloc redeclaration — the noalloc trees cannot import the
  allocating stdlib, so they must redeclare the externs they call (same class
  as the pre-existing `mimalloc.spl` entry), including the freestanding
  bare-metal runtime `bm_rt*.spl`, which IS the runtime for
  `<arch>-unknown-none` targets (nothing beneath it, same class as the
  2026-11-07 baremetal HAL providers).

`rt_db_*` C-engine bindings (`database/fast_db.spl`, `db/accel.spl`, and the
two opt-in CUDA bitmap adapters) are admitted as third-party-wrapper bindings
(same class as the `torch/` entries): the engine is C code reached only
through these externs; there is no Simple logic to migrate. This is distinct
from the Simple-implemented DB engine files named PRODUCT CODE in the
allowlist (`database/{core,mod,atomic,todo,checker}.spl`, etc.), which stay
forbidden below.

## Admitted: 98 files / 697 sites

Listed per file in the appended allowlist block
(`scripts/check/no_direct_rt_allowlist.txt`, section
"--- two-domain-tree provider tranche (2026-11-27) ---"). Families:

- io ABI leaves, category (a): `io/file.spl`, `io/pipe.spl`, `io/udp.spl`,
  `io/math.spl`, `io/thread.spl`, `tui/terminal.spl`, `fs/flat.spl`,
  `io/signal_stubs.spl`, `io/signal_handlers.spl`, `io/shared_parse_cell.spl`,
  `fs/nvfs_posix/{posix_driver,socket_nonblock}.spl`,
  `io/{tcp_read_span,http_get_core,disk_admission,profiler_simple,
  legacy_shell_contract}.spl`, `io/ws_client_core.spl`,
  `io/http_{client,server}_core.spl`, `io/browser_net_runtime.spl`
- Windows native-authoritative owners: the `windows_private_*`,
  `windows_broker_stdio_native_v1`, `windows_command_owner_v2`,
  `windows_engine_pipe_native_v1`, `windows_host_identity_v1`,
  `windows_local_process_principal_v1`, `windows_machine_policy_owner_v1`,
  `windows_process_owner`, `windows_pty_owner`,
  `windows_service_{incarnation,logon_namespace}_v1` leaves, plus
  `sosix/windows/contained_write_v1.spl`
- Linux/Darwin process + container owners: `linux_process_owner.spl`,
  `process_governor.spl`, `process_input_control_v1.spl`,
  `resource_scope.spl`, `linux_container_{containment,
  user_observation}_v1.spl`, `darwin_{snapshot,bound_image}_v1.spl`,
  `kernel_image_digest_v1.spl`, `local_ipc_v1.spl`,
  `piped_byte_endpoint_v1.spl`, `descriptor_stat_v1.spl`,
  `snapshot_links.spl`, `file_lock_owned_v2.spl`, `directory_roots_v1.spl`,
  `retained_file.spl`, `machine_authority_cleanup_v1.spl`
- Hardware-intrinsic / vendor-library ABI: `simd.spl`, `simd_crypto.spl`,
  `simd/profile.spl`, `engine/input/input_manager.spl`,
  `game2d/backend/sdl_backend.spl`, `web_ui/input.spl` (SDL2/SDL3/winit —
  same class as the allowlisted `io/simple_sdl3.spl` / `io/window_winit.spl`),
  `text_layout/font_{rasterizer,renderer}.spl`
- Runtime seams: `spec.spl` (SPipe BDD result surface: `rt_bdd_*`),
  `test_runner/{test_result_wrapper,test_executor_parsing,test_runner_coverage,
  test_runner_config,test_runner_fork,gpu_lane_common}.spl`,
  `dap/hooks.spl`, `mem/global_dataset.spl` (design-doc-named refcount
  surface), `crypto/entropy_platform.spl`, `src/core/random.spl`,
  `tls/certificate.spl`, `ui/host_frame_clock.spl`, `lsp/main_wasi.spl`
  (WASI fd entry shim), `platform/host_io.spl` (design-doc-named platform
  owner), `container/.../workspace_{storage_owner,executable_preparation}_v1`
  (native workspace-storage owners), `websocket/async_wire_hooks.spl`,
  `db/` + `database/` rt_db bindings (see criterion above), and the XRay
  seams `trace/xray_{win_flag_leaf,native_module,spy}_v1.spl` (each carries
  its own design/bug decision doc)
- noalloc forced redeclarations (class (e)):
  `nogc_async_mut_noalloc/baremetal/freestanding/{bm_rt,bm_rt32}.spl`,
  `nogc_async_mut_noalloc/tls/*` (seven "No-Alloc Baremetal Port" TLS 1.3
  files redeclaring the runtime crypto/transport externs they cannot import),
  `nogc_async_mut_noalloc/execution/watchdog_manager.spl` (owns the
  wall-clock watchdog extern by design),
  `nogc_async_mut_noalloc/kernel_plugin/allocation_probe.spl` (heap-registry
  introspection probe, same class as the allowlisted `mem/dump.spl`),
  `nogc_async_mut_noalloc/execution/semihost_capture.spl` (semihost test
  transport boundary)

## Deliberately left forbidden: 58 files / 283 sites (real product debt)

These do dispatch/parsing/policy/encryption/protocol/benchmark logic over raw
primitives where a typed owner or wrapper exists (or belongs to the
allowlist's explicitly-named PRODUCT CODE sets). They remain counted by the
ratchet at the 6290 baseline; each new site here still fails the gate.
Prescriptions for the follow-up migration lanes:

- `io_runtime.spl` (52) — self-documented workaround module ("works around
  the broken `use app.io.{...}` module import issue by declaring the extern
  functions directly"); 35 redeclared externs bypass the allowlisted
  `io/{file,dir,env,process,sysinfo,time}_ops.spl` owners. Prescription:
  consume those owners' typed wrappers (the import bug it cites must be
  filed/fixed rather than worked around — see the lane report).
- `trace/observer_native_channel_v1.spl` (50) — native retained-arena
  transport, but it redeclares `rt_par_atomic_*`, which
  `src/lib/nogc_sync_mut/atomic.spl` owns. Prescription: route through the
  atomic owner; note its `rt_ptr_*` calls already come via the allowlisted
  `ptr/` owner and still count because consumers calling raw names are
  counted — a renamed raw-address wrapper family in `atomic.spl`/`ptr/` is
  the structural fix (adding such wrappers is a public-API change outside
  this lane's constraints).
- `trace/observer_resident_{storage,owner}_v1.spl` (21) — arena allocation /
  singleton-control policy over raw alloc/atomic primitives.
- `debug/interpreter_backend.spl` (17) — explicitly named PRODUCT CODE in the
  allowlist (interpreter command dispatch).
- `storage_roots/{publisher,marker,path_policy}.spl` (23) — publication /
  marker / path-policy logic; should consume `io/file_ops`-style wrappers.
- `database/{core,todo,checker}.spl`, `database/server/capability.spl`,
  `database/vector/distance.spl` (7) — named PRODUCT CODE set.
- `benchmark/string_bench.spl` (7), `mcdc/{dynamic_probe,static_probe,
  probe_registry}.spl` (10) — benchmark / probe instrumentation logic.
- `redis/{server,client}.spl` (10) — RESP protocol logic over `rt_io_tcp_*`.
- `src/config.spl` (5), `env/{platform,config}.spl` (7),
  `env/{paths,system_location}.spl` (2), `platform.spl` (1) — config/env
  logic; `env_ops.spl` (allowlisted) is the env-primitive owner.
- `terminal/credential/{store,config_parser}.spl` (6),
  `terminal/power/{relay_power,host_power}.spl` (8),
  `terminal/relay_terminal.spl` (1) — credential encryption / power-automation
  logic.
- `enterprise_store/file_backend.spl` (4), `src/exp/{storage,sweep}.spl` (5),
  `src/math/backend.spl` (1) — storage/experiment/math-dispatch logic.
- `play/{launcher,page,electron_application}.spl` (6),
  `oidc/{discovery,id_token}.spl` (4), `js/node/fs_module.spl` (2),
  `security/kms_provider.spl` (1) — product client logic over process/HTTP
  primitives.
- `qemu/qmp_client.spl` (4) — QMP wire-protocol logic over unix-fd
  primitives.
- `test_runner/test_runner_execute.spl` (4) — mixed seam/file primitives.
- `io/{serial_proxy,telnet_serial_bridge}.spl` (5) — serial/telnet tool
  programs.
- `text_layout/font_provider.spl` (2) — font-fetch logic over process/HTTP.
- `spec/engine_probe.spl` (2) — engine probing over
  `rt_process_run_bounded` (process_ops facade).
- `daemon_sdk/{types,lock}.spl` (4), `service/lease_manager.spl` (1),
  `notebook/lane_locks.spl` (1) — daemon lease/liveness logic.
- `diag.spl` (3), `log.spl` (2), `hooks/stop.spl` (2),
  `cli_output/buffer.spl` (1) — logging/diag/hook output logic.
- `tls/_TlsUtilities/hex_encoding.spl` (1), `df/mod.spl` (1),
  `game2d/time/det_guard.spl` (1) — small logic leaves.

## Verification (measured 2026-11-27 on work/p3-sweep-20261127)

`sh scripts/check/check-no-direct-rt.shs --roots src` (lane evidence cache
`build/p3cache/ratchet/`):

- before: `FAIL — forbidden direct rt_* count 6926 exceeds baseline 6290
  (roots=src, src=6926), extern_decls=6720; top offenders:
  src/compiler/35.semantics/rt_criticality_validation.spl:211 ...`
  (per-file tally: `offenders-before.txt`, 1077 files).
- after: `PASS — 20087 file(s) scanned (roots=src, src=6229), forbidden=6229,
  extern_decls=6720 (baseline 6290)` with
  "note: forbidden count improved (6229 < baseline 6290)". allowed_provider
  6548 -> 7245 (+697 = the admitted tranche); offenders tally now 979 files
  (`offenders-after.txt`). Baseline file intentionally NOT regenerated: the
  improved headroom is left in place deliberately, per the bug doc's
  "not re-baselined" disposition — tightening to 6229 is a separate owner
  decision, not this lane's.
- committed HEAD was also measured (`--rev HEAD --count-only`): 6926 before,
  i.e. the overage was committed content, not concurrent worktree edits.
- `--selftest-only`: PASS (24 fixture classes incl. rg-vs-grep parity).

Measured two-tree raw `rt_*` line counts for the bug doc's own metric
(`grep -r 'rt_' <path> --include='*.spl' | grep -v '^ *//' | wc -l`):
nogc_sync_mut 11803, nogc_async_mut_noalloc 434. That metric counts
everything (including allowlisted providers, declarations, comments-safe
lines and naming-convention matches), so it moves only when the underlying
forbidden debt is migrated; it is not the enforced gate's population.
