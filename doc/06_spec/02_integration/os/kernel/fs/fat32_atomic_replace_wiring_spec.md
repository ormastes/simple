# FAT32 atomic-replace integration wiring

This executable integration check binds the fixed journal protocol to four
production owners: the disk provisioner, pre-publication FAT32 mount recovery,
the exact database rename adapter, and fail-closed database capability report.
It also confirms ordinary `rename_at` remains the documented non-atomic path.

The check is source/build wiring evidence only. Power-cut convergence and an
acknowledged generation read from a new QEMU process remain required by the
companion system manual.
