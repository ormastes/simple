# SimpleOS primary tool manifest

## Authenticated artifact receipts

Every tool is admitted independently through
`simpleos_primary_tool_receipt_v1`. The signed payload is bounded to 4096 bytes
and binds the tool name, canonical filesystem path, artifact digest, target,
filesystem, behavior contract, receipt id, signing key id, validity window, and
nonce. Verification is Ed25519 against the loader-configured trust root and
fails closed for missing/malformed signatures, unknown keys, stale/future or
overlong windows, invalid targets, and malformed identities.
The verifier owner reconstructs a domain-separated, length-prefixed canonical
body from every typed receipt field. Both the carried payload and any caller
expectation must exactly equal those bytes before signature verification, so an
arbitrary signed payload cannot be attached to substituted metadata. Successful
admission atomically consumes the bounded `receipt_id:nonce` replay key; reuse,
store exhaustion, expiry, and future issuance fail closed.

A verified receipt is not executable authority. The loader must separately
hash the bytes read from the mounted filesystem, compare that digest and all
receipt bindings, consume a live loader-owned authority token, and only then
spawn the process. Source modules, package projections, serial markers, fixed
commands, and host-side execution cannot satisfy this contract. Until those
target artifacts and live receipts exist, canonical manifest rows remain
`Blocked`; this lane makes no bootstrap or guest-execution claim.

`simpleos_primary_tool_manifest_v1` is the closed, versioned declaration for
primary userland categories: administration, archive/compression, networking,
checksums, text processing, process monitoring, and package management.

Rows are declared data, never inferred from source or package presence. A row
may become Supported or Partial only after evidence-service admission records
the exact owner, artifact digest, three target triples, FAT32/DBFS/NVFS
operation evidence, version/help behavior, and negative/error behavior.

The selected v1 inventory is exact and closed:

| Category | Executable identities | State |
|---|---|---|
| administration | no admitted executable | `Unavailable` |
| archive/compression | no admitted executable | `Unavailable` |
| networking | no admitted executable | `Unavailable` |
| checksums | `/usr/bin/sha256sum`, `/usr/bin/md5sum` | `Blocked` |
| text processing | `/usr/bin/grep` | `Blocked` |
| process monitoring | `/usr/bin/ps` | `Blocked` |
| package management | no admitted executable | `Unavailable` |

The three blocked categories have real pure-Simple owners and bounded behavior:
checksum and grep read through `VfsManager.read_bytes_bounded` with a 64 MiB
per-file limit, 64 KiB chunks, and at most 128 files; `ps` consumes the one
`list_tasks` owner, capped at 256 tasks and 32 command arguments. Their package
identities intentionally carry empty artifact-digest and admission-receipt
fields. The launcher returns exit 126 and `loader_authority_state=absent` for
these known files, or 127 for an unknown identity. It never treats that text
state as an executable-authority token and never falls back to an in-process
shortcut, PATH lookup, alias expansion, background execution, or pipeline
execution. The generic `launcher_launch_path_with_args` boundary also rejects
all four canonical paths before process spawn. It compares lexically normalized
absolute paths, so equivalent spellings with repeated separators, `.` segments,
or `..` segments cannot bypass the gate. Async and non-shell launcher callers
therefore cannot bypass the tool-specific gates.

Promotion requires target-native bytes at the exact canonical path, a lower-case
SHA-256 digest of those bytes, an evidence-service admission receipt, and a live
loader-owned `ExecutableAuthorityTokenV1` consumed by the loader. Source
presence, a package record, an empty digest/receipt, or a copied diagnostic
value cannot authorize launch.
