# NVFS connector path boundary v1

The hosted NVFS connector is a prerequisite test surface for the shared
FAT32/DBFS/NVFS VFS contract. Before executable bytes can safely be selected by
path, a mount must not claim a textual sibling such as `/nvfs-other`.

Mount and operation paths are canonical absolute paths without traversal, dot
aliases, or duplicate separators. A non-root mount path additionally cannot
end in a trailing slash. An
operation path must be absolute and is contained only when it equals the mount
path or its next byte is `/`. Root mounts accept absolute paths unchanged.
Existing dot-dot traversal rejection remains authoritative. Canonical root
paths are passed to the driver unchanged only after these validations.

Validation is O(n) in path bytes because it performs a bounded number of text
scans. The segment-boundary check materializes one one-byte slice and makes no
full-path copy. The change preserves all public APIs and does not overlap the
MountTable file-object lifecycle owner. It does not claim NVFS execution or add
a connection-lifecycle/security capability.
