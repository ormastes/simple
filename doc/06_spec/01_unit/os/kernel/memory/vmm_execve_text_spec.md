# VMM copied execve text specification

Status: authored, execution and docgen `MissingEvidence`.

Executable: `test/01_unit/os/kernel/memory/vmm_execve_text_spec.spl`.

The production decoder receives already-copied bytes and must preserve UTF-8
for `é` and an emoji, retain empty text, and reject surrogate UTF-8 with
`EINVAL` and empty error text. Consumed-byte counts include the NUL consumed
by its caller. Fixtures call the production terminal decoder directly; they
do not exercise VMM translation, user-copy faults, MMIO or guest syscalls.
