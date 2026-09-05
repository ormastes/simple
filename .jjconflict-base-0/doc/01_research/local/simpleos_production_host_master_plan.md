# SimpleOS Production Host-OS Master Plan — Local Repo Mapping

Saved: 2026-07-27. Domain doc:
`doc/01_research/domain/simpleos_production_host_master_plan.md`.
Plan: `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md`.

## Where the plan's subsystems live today

| Plan area | Repo location (canonical-to-be) | Current status |
|---|---|---|
| Kernel ABI | `src/os/kernel/abi/` | exists — extend with `*_v1.spl` contracts |
| IPC | `src/os/kernel/ipc/` (+ `l4_fast_ipc.spl` model) | model/benchmark, not syscall-integrated |
| Loader / FS-exec | `src/os/kernel/loader/`, `fs_exec_fallback_contract.spl` | per-exec bootstrap scheduler; ambient `spawn_full()` |
| FD/process | `src/os/kernel/fd_table.spl`, `fd_io.spl`, `lifecycle/` | partial; no global job/process model |
| Memory/pager | `src/os/kernel/memory/` | partial; no VMO/VMAR/pager objects |
| VFS/FS | `src/os/kernel/fs/` + direct FAT32 + old VfsManager | THREE overlapping stacks |
| Drivers | `src/os/drivers/` | evidence-contract heavy; no DeviceGrant runtime ABI |
| SOSIX/POSIX | `src/os/posix/`, `src/os/libc/`, `src/os/linux_personality/` | POSIX excludes shared mmap + pthreads |
| TTY/shell | `src/os/kernel/` tty paths, `src/os/apps/` shell | `tty_write()` doesn't deliver to endpoint |
| SSH | Simple-native SSH in `src/os/` | x86-64-only FS-exec arms; experimental |
| Containers | container contract + 8-slot namespace registry | metadata/markers, not enforcement |
| Web server | `src/os/http/`, `http2/`, `http3/` + native bench | routed server interpreter-bound |
| DB | embedded SDN store; server absent | SQLite port not started |
| Config | IDE SDN layered config | parser/getters hand-duplicated; no `std.config` |
| Browser | browser tree (see browser hardening research docs) | prototype; isolation gaps |
| LLM profiles | role/CSpace research docs | not wired to spawn-time CSpaces |
| Evidence | `.spipe/` states, SDN receipts, spec gates | some fail-open artifact checks |

## Related existing research/plans (do not duplicate)

- `doc/01_research/domain/simpleos_filesystem_toolchain_servers.md`
- `doc/01_research/domain/simple_web_browser_production_hardening.md` (+ engine variant)
- `doc/01_research/domain/riscv32_riscv64_fpga_simpleos_production.md`
- `doc/01_research/domain/wm_gui_web_2d_host_env_hardening.md`
- `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
- `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md`
- `.claude/rules/board-runnable.md` — QEMU-only results are defects unless scoped

## Local constraints that shape the plan

- Default tooling = self-hosted `bin/simple`; seed is bootstrap-only.
- jj on main, no branches; parallel sessions force-push — plan must use
  disjoint file ownership per agent to avoid the documented clobber class
  (see MEMORY: sync-clobber, jjconflict-tree incidents).
- Extern additions require bootstrap rebuild (`feedback_extern_bootstrap_rebuild`).
- Formal core: Lean4 already used (cache-identity Option-C); reuse for §21 invariants.
- Evidence receipts already SDN-based; fail-closed rule must be added where
  browser review found artifact-absent passes.
