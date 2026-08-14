<!-- codex-design -->
# RV64 Sv39/PID1/Network/SSH/WM Boot Completion Detail Design

## Scope and intent

This is authorized low-level compiler and operating-system implementation in a
private repository. The work is boot sequencing, self-hosted compilation,
syscall ABI plumbing, bounded IPC transport, process execution, framebuffer
presentation, QEMU system testing, and evidence retention. It is not exploit
development, credential collection, persistence, scanning, or access to an
external system. SSH is an in-repository guest service exercised only through
the loopback QEMU fixture and its fixed test credentials.

The canonical acceptance contract is AC-1 through AC-10 in
`doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`. This design does not
weaken or replace those criteria.

## Existing architecture decision

No new architecture or UI is introduced. The completion lane composes existing
owners:

1. the pure-Simple compiler owns Stage 3/4 production;
2. paging owns SATP activation/readback;
3. the process manager owns PID1 and process liveness;
4. VirtIO owners produce TX/RX/service facts;
5. the SSH daemon owns bind, session completion, filesystem exec, stdout, and
   return-to-accept results;
6. kernel IPC owns copied request/reply transport and scheduler transitions;
7. the compositor, desktop shell, WM producer, and Engine2D executor own the
   first PID-correlated frame;
8. `Rv64BootGateRuntime` is the sole ordered receipt composer;
9. the host SSpec owns the terminal verdict and retained evidence.

The pattern is owner-result composition. Each mutable owner returns a typed
fact; the boot orchestrator validates and commits that fact in order. Agents
must not add marker proxies, canned command output, synthetic surfaces, or a
second renderer/process/IPC path.

## Frozen interfaces

Agents consume these names and may not rename them independently:

- `Rv64BootGateState`, `Rv64BootGateObservation`
- `rv64_boot_gate_advance`, `rv64_boot_gate_verdict`
- `prepare_rv64_boot_gate_fixture`, `check_rv64_boot_gate_transcript`
- `Rv64BootGateRuntime.observe_sv39`, `.observe_pid1`, `.observe_network`,
  `.observe_sshd_ready`, `.observe_ssh_progress`, `.observe_wm`
- `rv64_sv39_activate_and_readback`
- `rv64_pid1_create_and_confirm_live`
- `rv64_network_init_facts`
- `SshDaemon.bind_and_ready`, `SshDaemon.accept_and_handle_once_result`
- `riscv64_fs_exec_spawn_capture`
- `Rv64SyscallState`, `IpcSyscallState`
- `_handle_ipc_send_state`, `_handle_ipc_recv_state`,
  `_handle_ipc_create_port_state`, `_handle_ipc_connect_state`
- `IpcManager.port_is_owned_by`, `.port_has_service_name`, `.send_owned`,
  `.recv_owned`
- `_vfs_ipc_request`, `VfsService.dispatch_message`, `VfsService.send_*_reply`
- WM/Window `_ipc_send` byte-zero wire helpers
- `Rv64ProductionWmProducer.launch`, `.pump_one_published_action`,
  `.snapshot_published_scene`, `.present_snapshot`
- `rv64_wm_scanout_metadata_valid`, `rv64_wm_snapshot_facts_ready`

Frozen operator steps:

- `step("Build admitted RV64 boot image")`
- `step("Boot QEMU and capture ordered lifecycle receipts")`
- `step("Prove OpenSSH login, exec, rejection, and accept-loop recovery")`
- `step("Prove process-owned WM readiness")`

Unavailable evidence stays fail-fast through `fail(...)`; it never becomes a
passing skip.

## Boundary and ownership table

| Boundary | Canonical owner | Data classification | Bound/invariant | Consumer |
|---|---|---|---|---|
| Stage2 -> probe | bootstrap checker | immutable executable handle + hash-bound receipt | candidate/runtime/checker/fixture hashes | compiler localization lane |
| syscall -> scheduler | RV64 dispatcher | owner-returned state value | returned scheduler must replace caller copy | launcher/boot owner |
| task -> IPC queue | kernel IPC syscall owner | encoded copied payload | `arg4 == IPC_COPIED_SERVICE_TAG` is the only copied-ABI selector; every other value is legacy. Named source emits raw reply <=4096; anonymous source emits `method(u32 LE)|payload` <=4100; reject before user-byte copy | VFS/WM/service owner |
| IPC discovery -> service | port registry | registered name + owner task | non-empty name <=64 bytes and unique; numeric port is never a PID | VFS/WM/service owner |
| IPC reply port -> PID | kernel port registry | authenticated task handle | live named/unnamed port owner, never numeric-port inference | WM service |
| process -> stdout | RV64 capture owner | bounded copied bytes | first 4096 bytes + actual status + truncation | SSH channel |
| compositor -> producer | frozen scene snapshot | frozen share | one PID, one scene revision, visible owned surface | Engine2D executor |
| executor -> scanout | typed revision receipt | owner result | presented revision matches scene; generation > 0 | boot gate runtime |
| guest -> host | serial/OpenSSH logs | retained encoded evidence | exact order, exactly once, correlated sessions | transcript checker/SSpec |

## Error and fail-closed behavior

- A probe build signal, ordinary build failure, missing executable, runtime
  signal, runtime nonzero exit, and output-contract mismatch are distinct.
- Invalid/missing IPC ports fail before blocking or consuming a message.
- Legacy IPC calls retain the existing method/flags ABI. Service messages use
  a sender-owned reply port and copied encoded bytes. The two forms must have
  explicit tests and must not be guessed from a payload after it is read.
- Oversized service messages fail before userspace copying.
- Named service ports are unique and have a kernel-recorded owner. A claimed
  source port must belong to the current task; service/request mode is selected
  from that live port classification, never guessed after reading a payload.
- `IpcDestroyPort` is owner-only self-revocation: a missing or foreign port
  fails without changing queue state. Copied service traffic is selected only
  by `IPC_COPIED_SERVICE_TAG`; a zero-length legacy send remains legacy.
- VFS requests are `method(u32 LE)|payload` from an anonymous reply port;
  named VFS replies are raw `status(i32 LE)|payload`. Both `wm_codec` and the
  Window helper pass the first byte, not the 16-byte Simple array header, to
  `SYS_IPC_SEND`.
- `fd_io._vfs_ipc_request`, `wm_codec`, and the Window helper explicitly add
  the 16-byte Simple byte-array header offset before `SYS_IPC_SEND`, so each
  sends item zero rather than runtime metadata. The focused VFS and WM wire
  specs remain required after TODO667 before this source-complete convention
  can be treated as executable evidence.
- A failed process launch cannot publish a PID or mutate a discarded scheduler
  copy.
- SSH readiness requires bind/listen; session progress requires completed
  handling and return to the accept-loop frame.
- WM readiness requires live PID, PID-owned visible surface, stable scene
  revision, matching Engine2D present, successful display present, and positive
  scanout generation.
- Any missing/reordered/duplicate lifecycle observation prevents terminal PASS.

## Terra evidence boundary (2026-08-14)

The current retained compiler discriminator is a blocker, not an admitted
runtime. The three-fixture receipt
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-054ce576790256e0-25383b77-1ed81de7-f44536be-93ec88d0/result.env`
is `FAIL-FAIL-FAIL` with every failure classified `build_sigsegv`; its later
five-fixture expansion
`build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-5c722174dfee3cf8-25383b77-dd975615-26b60e80-1ed81de7-f44536be-93ec88d0/result.env`
also fails its newly added plain baseline and struct controls. Both bind the
same unchanged Stage 2 candidate hash. They localize only a general native
build failure and must not admit a Stage 4, a compiler patch candidate, or a
QEMU lifecycle result.

Terra focused observations are deliberately narrower. The IPC handoff focused
spec and the `ssh_live_entry.spl`/WM-resource checks were reported PASS by the
wave, while the system SSpec invocation segfaulted during shared-checker load.
The PASS observations exercise bounded source-level slices only; the SSpec
failure means no checker-loaded scenario result and no live claim exists. Each
must be rerun once with a provenance-admitted Stage 4 before it can satisfy an
AC. The commands, artifact requirements, owner, and reviewer handoff remain
the canonical plan's verification ledger and TODO806--TODO809.

## Parallel implementation waves

### Wave P0 — design freeze (merge owner only)

Publish this design, the canonical AC plan, frozen interfaces, file ownership,
exact commands, and fail-fast rules before dispatch. No sidecar edits occur
until P0 is visible.

### Wave P1 — four independent jobs

| Agent | Bounded job | Exclusive files | Completion evidence |
|---|---|---|---|
| A: compiler localization | Validate the three-probe checker and, once per new hash-bound revision, distinguish scalar control, exact receiver, and adjacent push. Select a compiler fix only from trace/probe evidence. | Stage3 checker, three native fixtures, Stage3 bug record; `method_calls_literals.spl` only after proof | three independent receipts, localization, unchanged candidate hash; or exact blocker handoff |
| B: kernel/IPC/VFS wire integration | Preserve SpawnBinary scheduler state, destroyable owned ports, named-port discovery, legacy request ABI, owned service request/reply encoding, bounded payload copy, public/FD VFS routing, and receive behavior. | RV64/generic IPC syscall, IPC manager, `fd_io`, VFS service/manager, public FS/mount facades, focused IPC/VFS specs | source integrated; one post-Stage4 wire run remains required |
| C: boot/SSH/WM composition | Review typed Sv39/PID1/network/SSH/WM owner results and the one serial convergence path. No alternate desktop fixture. | boot runtime/entry, SSH process/stdout path, WM producer/resource adapters, `src/os/services/wm/wm_codec.spl`, `src/os/userlib/_Window/ipc_helpers.spl`, focused specs | no synthetic/canned path; source review plus focused results after Stage4 |
| D: SSpec/docs/evidence | Keep AC map, manual, guide, expert handoff, TODO rows, and exact artifact paths aligned with executable source. | canonical plan/task/manual/guide/wikis and existing TODO666/667/806-809 only | unique TODO rows, referenced paths exist, zero layout/stub issues; docgen after Stage4 |

No two agents edit the same file. A cross-lane interface change is sent to the
merge owner and applied serially after both owners agree.

### Wave P2 — serial convergence

The merge owner reviews the complete diff, reconciles cross-lane types and
calls, runs bounded static gates once, and commits. If an admitted Stage4 exists,
the owner then runs the focused ledger once. Otherwise executable/live evidence
remains on the existing Todo rows.

The current dirty IPC/VFS/WM wire changes reopen B/C source-integration review:
they strengthen the intended contract but have no retained source-matched
one-run result. They must not be summarized as a completed B, C, E, AC-3/6, or
AC-5 lane until their focused rows below pass on TODO667's admitted CLI.

### Wave P1b — VFS lifecycle and semantic convergence (source integrated)

The copied IPC review found three owner gaps that converge before P2:

| Agent | Frozen interface / job | Exclusive files | Required result |
|---|---|---|---|
| H: reply-port lifecycle | Add syscall 18 `IpcDestroyPort` and `IpcManager.destroy_port_owned(task, port_id) -> bool`; destroy only the current task's live port and release queue state deterministically | IPC manager, generic/RV64 syscall dispatch/types, focused IPC lifecycle specs | create/connect/send/receive/destroy does not consume the bounded port table; wrong-owner/missing destroy fails |
| I: public FS wire semantics | Make `vfs_ipc_request_bytes` close its reply port on every terminal path; implement `read_text`, `write_text`, `stat`, and `readdir` against the service's binary OPEN/READ/WRITE/STAT/READDIR/CLOSE formats | userlib fs/mount facade and focused wire specs | exact method IDs, payload widths, binary decoding, and close-on-success/failure contracts |
| J: VFS manager routing | Route mutation handlers through `VfsManager`; add the missing manager `chmod` owner and enforce existing grant/container/read-only rules consistently | `services/vfs/vfs.spl`, `vfs_service.spl`, focused manager/service specs | no direct mounted-filesystem bypass in unlink/rmdir/rename/chmod/symlink handlers |
| K: kernel FD data path | Route file descriptors from `posix_read`/`posix_write` through copied `VFS_READ`/`VFS_WRITE` using the stored backend handle; preserve pipe/socket/serial routes and advance the FD offset only by actual bytes | `kernel/fd_io.spl`, focused FD/VFS specs | OPEN -> READ/WRITE -> CLOSE uses one VFS handle, bounded chunks, exact byte copies/status, and closes every transaction reply port |

H publishes the destroy syscall as a frozen consumer interface. I may code
against that named interface while H implements it. J does not edit IPC or the
user facade. The merge owner resolves any visibility change serially.

### Wave P1c — explicit IPC ABI and close convergence

| Agent | Frozen interface / job | Exclusive files | Required result |
|---|---|---|---|
| L: explicit copied-message tag | Define `IPC_COPIED_SERVICE_TAG = 0xFFFFFFFFFFFFFFFFu64` in the syscall owner. `arg4 == TAG` selects `(dst, source_port, byte_ptr, byte_len)`; every other `arg4` uses legacy `(dst, method, flags, ptr, len)`. Remove port-ID heuristics. | IPC syscall owner plus copied-service producers and focused ABI specs | zero-length legacy sends remain unambiguous; all copied producers pass TAG |
| M: idempotent VFS close | Add an idempotent service/manager close owner. A confirmed close or already-retired handle is success; transport failure preserves the final local FD for retry. `dup2` retains POSIX local replacement semantics while recording remote cleanup failure. | VFS manager/service, kernel fd owner, focused close specs | lost reply can retry without leaking or permanently retaining a stale FD |
| N: SOSIX VFS convergence | Replace fixed-endpoint legacy `sosix/io.spl` and `io_rw.spl` requests with the shared named copied VFS request owner and current method/payload/reply formats. | SOSIX I/O files and focused SOSIX/VFS specs | no private VFS method/payload path remains |

L freezes the tag before producer edits. M and N consume the current copied
request helper and do not create another transport. All three lanes preserve
the 4096-byte payload and reply-port lifecycle bounds.

The retained dirty source now implements this wave, subject to the execution
boundary below. `IpcDestroyPort` is syscall 18 and delegates to
`IpcManager.destroy_port_owned`; it rejects a missing or foreign port, wakes
waiters deterministically, drains queue state, and leaves monotonic port IDs.
The service ABI registers unique non-empty names, authenticates the live source
port before copying user bytes, and distinguishes anonymous
`method(u32 LE)|payload` requests (at most 4100 bytes) from named-service raw
replies (at most 4096 bytes). `fd_io` now addresses byte-array item zero after
the 16-byte Simple header, creates and destroys an anonymous reply port on
every terminal path, decodes raw `status(i32 LE)|payload`, and routes
OPEN/READ/WRITE/SEEK/CLOSE by stored VFS handle with bounded chunks and actual
byte-count offset advancement. The VFS handle table retains bounded terminal
close knowledge through its monotonic issue watermark: an issued-but-retired
handle is an idempotent close success, while zero/future handles still fail. A
lost transport reply keeps the final local FD retryable; `dup2` performs its
required local replacement while recording remote cleanup failure. POSIX
access-mode flags reject reads from `O_WRONLY` descriptors and writes from
`O_RDONLY` descriptors; `pread` restores both remote and local cursor.

The public facade implements binary `read_text`, `write_text`, `stat`, and
`readdir` request/reply decoding and closes its reply port on both success and
failure. `VfsManager` now owns chmod and mutation routing, including mount
boundary, grant/container, and read-only checks. SSH sessions use the real
filesystem-exec result lifecycle rather than a canned combined-command path;
the existing bounded stdout/status capture remains attempt-local. WM and
Window IPC helpers likewise pass the first array item, not the runtime header.
Focused specs are source evidence only until TODO667 admits the runner:
`test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl`,
`test/01_unit/os/kernel/ipc/ipc_port_destroy_spec.spl`,
`test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl`, and
`test/01_unit/os/wm/wm_window_ipc_wire_contract_spec.spl`.

### Wave P3 — evidence execution after compiler admission

After TODO666 produces Stage3 and TODO667 produces the admitted Stage4 CLI,
independent agents may run disjoint focused rows. The live QEMU row is serial
because it owns fixed host ports and canonical artifact paths. Docgen follows
the focused SSpec and maintain scan, not the live QEMU result.

## Agent prompt contract

Every parallel prompt must state:

1. “Functional low-level compiler/OS implementation in the named local files
   of this private repository; no network activity.”
2. The exact AC IDs and frozen interfaces it implements.
3. Exclusive writable files and prohibited files.
4. Exact input artifacts and authoritative owner results.
5. One-run verification commands and the three-fix-cycle ceiling.
6. No Rust seed, synthetic receipt, canned output, marker proxy, alternate
   renderer, or unrelated TODO creation.
7. Required handoff: files, commands, outputs, retained artifact paths,
   unresolved blocker, merge owner, and highest-capability reviewer.

## Verification mapping

| Requirement | Focused evidence | Final evidence |
|---|---|---|
| AC-1 | three native localization probes; exact + adjacent fixed regression | admitted Stage3 lineage |
| AC-2 | essential test/lint/duplicate/aggregate markers | admitted/deployed/rollback Stage4 hashes |
| AC-3/6 | boot-gate unit/runtime/system checker specs | ordered retained serial verdict |
| AC-4 | stdout capture and SSH contract specs | independent OpenSSH outputs/status and accept recovery |
| AC-5 | IPC, WM resource/adapter/producer specs | PID/scene/revision/scanout/QMP evidence |
| IPC/VFS wire delta | destroy-port, syscall-handoff, RV64 syscall IPC, public VFS wire, manager-route, FD/VFS, and WM/Window wire specs | retained focused outputs before AC-3/5/6 can be accepted |
| AC-7 | focused SSpec, maintain seven scores, zero-stub docgen | reviewed canonical manual |
| AC-8/9 | plan/task/guide/wiki/bug consistency checks | final highest-capability review |
| AC-10 | static guards, one-run ledger, commit/rebase/push | reachability, clean intentional tree, done receipt |

## Stop conditions

- Never repeat an identical failed command.
- At most three fix cycles per criterion.
- Stop a lane when its owned implementation and one allowed verification pass
  converge.
- A missing admitted Stage4 blocks executable evidence, not unrelated source
  implementation.
- A crash without a symbolized trace does not authorize a speculative compiler
  owner edit; retain the discriminator and existing Todo handoff instead.
