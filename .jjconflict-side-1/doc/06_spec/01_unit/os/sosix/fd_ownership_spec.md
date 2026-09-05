# SOSIX file descriptor ownership

Executable specification: `test/01_unit/os/sosix/fd_ownership_spec.spl`

The ownership record keeps the original owner authoritative while a transfer
is pending, changes ownership only on explicit completion, and restores the
held state on cancellation. Closing a record increments its generation, so a
stale handle cannot observe or mutate the next record that reuses the slot.
