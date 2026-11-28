# x86 cpu.spl re-declared raw CR3 externs, bypassing runtime_hal

- Status: verification-pending (fix landed; native/real-binary spec run not yet possible, see Evidence)
- Lane: ft29-10
- Spec: `test/01_unit/os/kernel/arch/x86_runtime_hal_boundary_spec.spl`

## Defect
`src/os/kernel/arch/x86_32/cpu.spl` and `x86_64/cpu.spl` each declared their own
`extern fn rt_read_cr3` / `rt_write_cr3` and called them directly, duplicating the
typed raw owners `x86_32/runtime_hal.spl` and `x86_64/runtime_hal.spl`
(`hal_x86_NN_read_cr3` / `write_cr3`). The x86_32 copy also disagreed on the
write ABI width (`u32` vs the authoritative C `uint64_t`).

## Which side was wrong
The code. `doc/07_guide/os/hal/pure_simple_hal.md` sec. 1 makes the runtime a
boundary with a single typed owner. The CR3 assertions in the spec were right.
Parts of the spec were stale and were corrected:
- port aliases (`hal_x86_NN_port_inb as port_inb`): port I/O is owned by
  `os.kernel.arch.x86.port_io_owner` per `x86_runtime_owner_contract_spec.spl`;
- `paging.spl` `hal_x86_64_{read,write}_cr3` expectations: paging deliberately
  goes through `vmm_core._load_cr3` and must not mention `read_cr3` (same owner spec).

## Fix
Both cpu.spl files now `use ...runtime_hal.{hal_x86_NN_read_cr3 as read_cr3,
hal_x86_NN_write_cr3 as write_cr3}`; the raw externs are gone. `read_cr3` keeps a
real read path (`rt_read_cr3` in runtime_hal).

## Prevention
New spec `it` "declares raw CR3 externs only in the per-ISA runtime_hal owners"
checks every x86/x86_32/x86_64/arch_adapt source mentioning CR3.

## Similar pattern, out of scope (follow-up)
`src/os/kernel/memory/vmm.spl:469` still declares `rt_read_cr3`/`rt_write_cr3`
(multi-arch file; vmm_core already routes via `os.kernel.hal.runtime_hal`).
`src/lib/nogc_sync_mut/sffi/host.spl` also declares them.

## Evidence
`bin/simple.exe` here is the Rust seed; in this lane's environment every
`file_read`-based example in this spec (including pre-existing ones) fails with
`text_byte_buffer ... function Capacity not found`, so the spec could not be
executed to green. The edits were verified by grep against each assertion.
