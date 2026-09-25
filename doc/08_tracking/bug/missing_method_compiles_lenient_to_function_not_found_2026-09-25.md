# Missing struct method compiles leniently to `rt_function_not_found` (silent wrong-value call)

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up); affects every lane
that compiles with the self-hosted compiler.
Severity: silent wrong answer — a call to a method that does not exist on
the receiver type builds successfully, runs, prints a `[WARN] unresolved
fn:` line (easily lost in serial noise), and returns NIL, which the caller
then uses as a real value.

## The gap

`src/os/services/vfs/vfs_boot_state.spl:488` called
`table.positioned_fstat(handle.id)` on a `MountTable`. No such method
existed anywhere in `src/lib` (verified by repo-wide search). The kernel
nonetheless compiled and linked: the call site was lowered to
`rt_function_not_found("MountTable.positioned_fstat", 27)` — visible in the
ELF as a literal-pool name + length feeding the runtime WARN-and-return-NIL
helper — and the caller continued with the NIL "Result", unwrapping it into
a garbage `FileStat` whose size field drove a 115 MiB allocation attempt.

The leniency that lets this ship is the same family as
`bare_statement_call_lenient_unresolved_global_2026-09-25.md`, but for
method dispatch: an unresolved method name does not fail the build; it
degrades to a runtime WARN + NIL.

## Concrete failure (Wall 7a of the aarch64 in-guest clang lane)

`MountTable.positioned_fstat` was called by the ARM mounted reader's
bounded read (`arm_fs_exec_vfs.spl`). The method had never been
implemented; the reader "fstat"ed a NIL box and fed the garbage size into
`alloc_zeroed_bytes`, which then died on the (separate) array_push
stale-store bug during the 115 MiB payload allocation
(run-20260925_182140: no fstat line, heap-exhaustion PANIC).

## Fix applied (2026-09-25)

`src/lib/nogc_async_mut/fs_driver/mount_table.spl`: implemented
`positioned_fstat` (bind the virtual handle via `_file_binding`, find the
bound mount by scalar `.id` compare, dispatch `_driver_fstat`), mirroring
`positioned_read_bytes` (56c8004b1eb).

## For the compiler lane

- Method-miss on a known receiver type should be a build error, not a
  lenient runtime fallback. If the leniency is required for dynamic
  dispatch, restrict it to dyn/erased receivers, not concrete struct types.
- Audit debt: any `rt_function_not_found` call site in a shipping ELF is a
  missing method that compiled clean. `aarch64-linux-gnu-nm <elf> | grep
  rt_function_not_found` plus a call-site scan names them; the WARN text
  itself (`[WARN] unresolved fn: <name>`) is grep-able in serial logs but
  was lost in this lane's output — do not rely on the runtime WARN as the
  detection mechanism.
