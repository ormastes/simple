# Detail design: SimpleOS filesystem toolchain and servers

## Loader flow

1. Canonicalize and open the requested mounted path.
2. Read/validate ELF header and bounded program-header table.
3. For each `PT_LOAD`, validate offsets/sizes, allocate pages, zero BSS, and
   read file-backed bytes directly into mapped frames in bounded chunks.
4. Build argv/env/auxv, enter ring 3, and report the real exit status.

## Image flow

- Build target-native static Clang and Simple payloads.
- Size FAT/initramfs from payload totals plus filesystem overhead.
- Write the validated bytes to all canonical paths and record the target build
  stamp in `/SYS/SIMPLETOOL.SDN`.
- Reject text, marker, empty, unstamped, wrong-entry, host-target, or missing
  payloads before staging.

## Server flow

- HTTP scenario: boot, send `GET /health` and `GET /`, assert status/body.
- DB scenario: use the same boot HTTP listener, send three `POST /db` requests,
  and require create, insert, and the selected known value in one boot.

## Error handling

Every build/boot/check wrapper returns nonzero for missing media, stale build
stamp, target mismatch, short reads, malformed ELF/query, timeout, guest fault,
unexpected preload use, or missing response.
## Restart12 deployment detail-design addendum (2026-08-14)

The planned owner is `scripts/check/check-simpleos-toolchain-desktop-boot.shs`.
It consumes an admitted image, validates the embedded/pre-boot image records,
launches OVMF CODE plus per-run VARS and GRUB EFI, selects
`gui_entry_desktop.spl`, captures desktop/scanout/framebuffer evidence, then
runs the literal guest version/emit-object/link/execute flow before shutdown and
emits the separate desktop/guest receipt. The frozen commands, helper names,
aliases, receipt fields, and fail-closed policy live in the canonical x86_64
plan; the wrapper remains B-DESKTOP-LIVE until implemented.
# Guest filesystem Hello World evidence boundary

`os.port.guest_filesystem_hello_receipt` is a typed non-authorizing projection for the
guest-native C smoke workflow. It binds Clang and LLD to absolute guest paths,
binds all intermediate paths to the selected FAT32, DBFS, or NVFS mount, and
requires the actual target Clang, LLD, source, object, and target ELF bytes
alongside their digests. Missing artifacts, PATH lookup, host execution, cross-filesystem path
substitution, wrong-machine ELF output, non-zero exits, and output substitution
are hard failures. Caller booleans and transcripts are not authenticated
evidence: even a structurally consistent forged candidate cannot authorize
guest execution. Only the external evidence-service owner may combine its
authenticated handle with a loader-owned consume-once token and commit a ledger
result.
