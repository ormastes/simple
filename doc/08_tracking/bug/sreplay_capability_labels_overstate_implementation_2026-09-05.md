# SReplay capability labels overstate implementation (2026-09-05)

Source-verified truth reset for `doc/01_research/infra/dump_replay/simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md`
§4.2. That table was produced by GitHub code search, not by reading the files.
This record re-checks each row against the actual source and states a verdict.
All seven rows are **CONFIRMED** — the design doc's relabeling is accurate, in
some cases understated (the code does even less than the doc implies).

## 1. SReplay process "recorder" -> `syscall-observation-prototype`

CONFIRMED. `src/lib/nogc_sync_mut/replay/process/recorder.spl:56-78` (`record()`)
shells out to `strace -f -tt -T -e trace=all` via `shell()` and parses text
output. Decisive: `extract_syscall_nr()` (line 271-273) is `# For now, return 0
— full syscall number mapping is a future enhancement` — it unconditionally
returns `0`. No syscall numbers are ever reconstructed from the trace.

## 2. SReplay process "checkpoint" -> `partial-process-state-prototype`

CONFIRMED. `src/lib/nogc_sync_mut/replay/process/checkpoint.spl`: `save_process_checkpoint`
(line 149) reads only `sp`, `pc`, `syscall_nr` from `/proc/<pid>/syscall` and up
to 20 `rw` memory regions via shell `cat`/`xxd`. `restore_process_checkpoint`
(line 198-219) writes pages back via `dd`, but for registers it only does:
`for reg in cp.register_state: print "[sreplay] Register {reg.name} = {reg.value}
(restore requires ptrace SFFI)"` (line 214-216) — register restore is
explicitly unimplemented, stated in the code's own print string.

## 3. Process reverse step -> `trace-navigation-prototype`

CONFIRMED. `src/lib/nogc_sync_mut/replay/process/replayer.spl:166-201`.
`reverse_continue()` finds the nearest checkpoint (`checkpoint_mgr.nearest_before`),
prints that it is "restoring" it, then does `self.cursor = restore_point` followed
by `while self.cursor < target_event: self.cursor = self.cursor + 1` — a pure
index walk over the in-memory event list. It never calls
`restore_process_checkpoint` or any process-state restore function. `reverse_step`
(line 198) is `self.reverse_continue(self.cursor - 1)`, i.e. the same cursor walk.

## 4. SimpleOS container checkpoint/restore -> `schema-and-orchestration-prototype`

CONFIRMED, and understated if anything. `src/os/kernel/replay/checkpoint/container_restore.spl`:
`restore_memory_page` (line 76-80), `restore_fd` (line 86-91), and
`restore_fs_entry` (line 97-101) are each literally `Ok(nil)` with a comment
block describing what "a real kernel" would do — not partial logic, no-ops.
`restore_process` (line 40-70) loops over register name/value pairs but only
reads them into unused locals (`_name`, `_value`) next to a comment
`# kernel_set_register(task_id, name, value)` that is never called.
`container_checkpoint.spl` mirrors this on the freeze side: "Phase 1: Freeze
scheduler ... (In a real kernel, would call scheduler.freeze_container())"
(line 19-20) and the matching thaw comment (line 41-42) — no scheduler call.

## 5. RV32 VM snapshot -> `cpu-register-snapshot-prototype`

CONFIRMED. `src/lib/nogc_sync_mut/replay/vm/vmem.spl:85-92` (`get_dirty_page_addrs`)
returns only page-aligned addresses, never the page contents. In
`replay_driver.spl:95-108` (`save_snapshot`), `device_states: []` is a literal
empty list every time. `restore_snapshot` (line 110-125) restores `cpu_pc`,
all 32 GPRs via `write_register`, and `cycle_count` — CPU state only; it never
reads `dirty_page_addrs` back into `VirtualMemory`, so memory is not actually
restored despite being tracked.

## 6. Replayable device bus -> `device-contract-prototype`

CONFIRMED. `src/lib/nogc_sync_mut/replay/vm/device_bus.spl` declares
`trait ReplayableDevice` (line 12-20) with `snapshot()`/`restore()`/`mmio_read`/
`mmio_write`, but `DeviceBus.entries: [BusEntry]` (line 26-30, 37) stores only
`name/base_addr/size/irq` descriptors — never a live object implementing the
trait. `grep -rn "ReplayableDevice" src/` across all three memory variants
(`nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`) finds only the trait
declaration and its `__init__.spl` re-export — zero `impl ReplayableDevice for
...` anywhere in the tree. `io_log` records MMIO read/write/interrupt events as
descriptor tuples, not device snapshot/restore calls.

## 7. SimpleOS kernel replay "zero cost when off" -> `runtime-switchable-near-zero`

CONFIRMED. `src/os/kernel/replay/mode.spl:46-55`: `g_replay_mode` is a plain
`var i32`; `replay_is_off()` is `g_replay_mode == 0` — a load + compare, run on
every call regardless of mode, never eliminated at compile time. The only test,
`test/03_system/tools/replay_offmode_overhead_spec.spl`, benchmarks 1000 hook
calls completing in `<100ms` wall time (lines 80-114) — a coarse latency bound,
not a binary-identity / codegen-elimination proof. No compile-time-off variant
exists in the tree.

## Verdict summary

All 7 rows: **CONFIRMED**, doc's proposed label accepted as-is (no corrections
needed). Row 4 and row 6 are arguably understated by the design doc — row 4's
restore functions are unconditional no-ops (not "mostly no-ops"), and row 6 has
literally zero trait implementations, not merely "descriptors only."

## Files changed as a result
- `doc/07_guide/app/tools/sreplay.md` — relabeled per-track capability wording.
- CLI/MCP help strings: none found overstating replay capability under
  `src/app/*/command_registry.spl` or a `src/app/replay|sreplay/` tree — see
  the "CLI/MCP help string audit" note below.

## CLI/MCP help string audit

`src/app/sreplay/` does not exist; `src/app/replay/` does
(`main.spl`, `record_session.spl`, `replay_session.spl` — Track 3 CLI). There is
one `command_registry.spl` in the tree, at `src/app/cli/command_registry.spl`
(the design doc's glob assumed one per app dir; adjusted to the real path).

`grep -n "reverse\|checkpoint\|replay\|full state\|deterministic"` over
`src/app/replay/{main,record_session,replay_session}.spl` and
`src/app/qemu/{commands,main}.spl` found only Track 3 (process rr, this lane's
subject) and Track 1 (QEMU icount replay, NOT one of the 7 flagged rows) help
strings. Track 3's own text is already honest: `record_session.spl:75` says
"Record a process execution for deterministic replay" (recording is real; only
the checkpoint/reverse-step layers built on top are prototypes, per rows 1-3
above) and `replay/main.spl:19` says "Replay a recorded process trace or
inspect a build replay log" — neither claims restore or backward execution.
Track 1's `qemu/main.spl:75` ("Replay replays it with GDB reverse-debug
support") is accurate for Track 1: QEMU's own `-icount rr=replay` deterministic
replay is a real, independent mechanism, not one of the seven rows under
review. **No CLI/MCP help string in this tree overstates a Track-3/5/6/kernel
capability** — the overstated wording lived entirely in the prose guide
(`sreplay.md`), which is fixed below. No string literal edits were needed.
