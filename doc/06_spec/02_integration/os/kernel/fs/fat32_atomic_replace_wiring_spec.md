# FAT32 atomic-replace integration wiring

Source: `test/02_integration/os/kernel/fs/fat32_atomic_replace_wiring_spec.spl`

Evidence class: `source-contract`.

This executable integration check binds the fixed journal protocol to four
production owners: the disk provisioner, pre-publication FAT32 mount recovery,
the exact database rename adapter, and fail-closed database capability report.
It also confirms ordinary `rename_at` remains the documented non-atomic path.

The filesystem assertions follow the current split owners under
`src/os/kernel/fs/_Fat32Filesystem/`: state, mount/read, allocation/write,
directory mutation, atomic-replace transaction, public mutation API, and mount
owner. Across those modules the check requires recovery before cache/publication,
payload/header/cursor/free ordering, all-FAT-copy repair and reread, exact root
directory replay bounds, bounded acyclic disjoint chains, serialized namespace
mutation with post-lock revalidation, and safe fixed V1 sector reservation.

The check is source/build wiring evidence only. Power-cut convergence and an
acknowledged generation read from a new QEMU process remain required by the
companion system manual.
