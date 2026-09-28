<!-- codex-architecture -->
# SOSIX positioned authority plane — TLDR

Status: proposed. The kernel-global MountTable and catalogue FAT32 `VfsManager` are separate providers with different handle identities. The kernel positioned shim currently has a backend route but no production installer for authenticated capability and owned-copy buffer registries.

The release path needs a live kernel-owned service identity, authenticated open and buffer-registration control operations, publication of each returned registry into the retained shim state, and retirement on close/restart. No request may choose its caller ID or borrow a handle from the other VFS domain.

`boot_nvfs_root_mount_transaction_v1` installs a route before committing its root. A stacked candidate quarantines the exact route on commit failure and retires prior registrations. End-to-end failed-commit and QEMU evidence, DBFS audit, and root-to-route publication binding remain pending.

Next: settle control operation IDs and F1/F2 write policy; implement the mount/route owner, registration transport, and shim publication; prove real task isolation, read/write, recovery, and retirement in QEMU. This draft supplies architecture only.
