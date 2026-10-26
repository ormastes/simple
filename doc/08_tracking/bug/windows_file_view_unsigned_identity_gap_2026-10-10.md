# Windows file-view identity cannot represent this host volume

Bug: `WINDOWS-FILE-VIEW-IDENTITY-20261010`

Status: confirmed source-contract incompatibility; native archive candidate
unrun, private and unapplied. No workaround admitted. Bug DB reconciliation
pending until the qualified DB owner is available.

The existing file-view API returns device/inode as nonnegative signed i64
values. The reviewed private Windows provider queries full FILE_ID_INFO and
correctly refuses lossless conversion when the unsigned volume exceeds
INT64_MAX or the 128-bit file identifier cannot fit its old inode field.
This refusal preserves safety but cannot deliver Windows archive support on
all volumes, including the observed host.

## Actual evidence

The executed retained-directory OS probe records FILE_ID_INFO bytes beginning
`adfeab223bac22f6`. Decoding the first eight bytes as little-endian u64 gives
volume `0xf622ac3b22abfead`, greater than `0x7fffffffffffffff`.
Both independent Win32 and NT probe fixtures observed this same volume.
The source candidate checks `out->id.VolumeSerialNumber > INT64_MAX` and returns
`-4`. This is a source-level consequence, not an executed archive failure.

Probe: `build/windows-retained-interpreter-adapter-20261010/nt-rename-cut1/probe-result.json`.
Probe source SHA256:
`ec4e75fcd83d837089bd6cb8a36b91848a3a8cf0c286aa0766802c916c50ff9d`.
Windows provider candidate SHA256:
`7ae59d41f3483368c55f89456d4be101f468706c20287cbf144e8a905b5f38f3`.

## Required fix and acceptance

Extend the existing native/pure capability boundary with an explicit versioned
identity result preserving all volume and 128-bit object identifier bits.
Keep the old signed compatibility methods fail-closed. Do not truncate, hash,
reinterpret an error sentinel as an identity or weaken beneath-root containment.
Migrate the actual read-only facade and pinned-archive consumer to the exact
identity owner rather than adding a second policy authority.

Author reproducing and prevention controls before implementation: observed
high-bit volume, low-bit volume, nonzero upper object-ID bits, all-zero or
unsupported identity, distinct objects differing only in upper bits, stable
retained identity across leaf replacement, changed identity refusal, stale
handle and close/read races. Run actual filesystem/archive boundaries with a
runtime bound to the new provider; constructed identity fixtures alone do not
qualify the host archive path.

Owners: Astra platform/projection lane implements; Astra formal lane reviews;
primary agent admits exact runtime evidence and connected TLDR consumers.
No full bootstrap or performance improvement follows from this report.
