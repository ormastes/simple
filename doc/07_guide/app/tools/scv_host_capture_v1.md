# SCV Host Capture V1

This version admits one explicit workspace-relative regular file through the
no-follow read-only file view, then asks SCV's content-addressed chunk owner to
store the exact bytes. Paths must use simple relative segments. Absolute paths,
parent traversal, `.scv`, symbolic links, unsupported filesystems, and files
larger than 16 MiB are refused. The root must be an initialized SCV workspace
whose `.scv` control directory resolves as a real directory.

`host-capture <path-relative-to-workspace>` returns a SHA-256 digest, byte
count, and content-addressed chunk ID after exact chunk readback. Repeating a
capture of unchanged bytes returns the same chunk ID. The result is
`captured_not_durable`: the bytes were observed in the local object store, but
directory-entry crash durability is not claimed. This API does not write a
journal event, so it does not claim a durable transaction receipt. The chunk
is not pinned by a file object or protected from later garbage collection.
The `.scv`, `.scv/objects`, and `.scv/objects/chunks` directories must already
exist and resolve to their expected workspace paths. This is a point-in-time
check. Keep the SCV control store and its ancestors under host-controlled
permissions while capture runs; the check does not protect against an
untrusted process racing a directory replacement.

`host-copy`, `host-move`, and `host-delete` are reserved command names and
return `unsupported` without reading or changing user paths. The current
filesystem layer has a safe descriptor-relative source reader but no
descriptor-relative mutation provider. A path preflight followed by a normal
write or unlink would leave a parent-swap race, so these operations remain
closed until the filesystem owner provides that capability.

The command adapter accepts:

```text
host-capture <path-relative-to-workspace>
host-copy <op-id> <source-relative-path> <destination-relative-path>
host-move <op-id> <source-relative-path> <destination-relative-path>
host-delete <op-id> <path-relative-to-workspace>
```

Command receipts use SDN key-value fields and include explicit
`durability_claim: false` and `journal_claim: false` values.

The application dispatcher supplies the workspace root. Command arguments
cannot choose an arbitrary root.
