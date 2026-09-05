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

- The dedicated launcher reads `/SYS/APPS/WEBSRV.SMF` and
  `/SYS/APPS/DBSRV.SMF` from the mounted filesystem and registers both images
  in one live kernel `Scheduler`. It must not call the blocking
  `x86_64_fs_exec_spawn_scheduler_owned` path twice: the first non-terminating
  server would prevent the second launch.
- Each server receives its exact single-worker `--simpleos` argv plus the same
  boot nonce. The scheduler owns distinct positive task IDs, address spaces,
  capabilities, and lifecycle records before either task enters ring 3.
- The launcher installs that scheduler in the x86 trap runtime and dispatches
  the first runnable task. Timer/syscall returns, rather than a synchronous
  kernel call stack, select the other runnable server.
- HTTP scenario: send two different `POST /render` payloads, assert status,
  `image/png`, valid PNG bytes, and different response bytes.
- DB scenario: send PostgreSQL v3 StartupMessage, SimpleQuery, and Terminate;
  restart the guest and prove a committed value survives.

### Launcher admission boundary

`SIMPLEOS_FS_SERVER_LAUNCHER_V1` is evidence only when a dedicated kernel
entry closure implements the scheduler-owned flow above. A marker embedded in
an otherwise unrelated kernel, two sequential blocking fs-exec calls, or web
and DB code linked into the kernel are rejected substitutes. Until the
dedicated entry and producer exist, the QEMU filesystem-launch scenario is
RED even if the server artifacts themselves cross-link successfully.

Before scheduler mutation, the launcher passes one immutable admission record
containing the two canonical filesystem paths, pinned artifact versions,
declared SHA-256 digests, FAT image identity/digest, launch nonce, exact
single-worker argument profiles, and runtime profile
`simpleos-single-worker-v1`. Ring 0 recomputes SHA-256 over both actual byte
arrays with the kernel-owned pure-Simple implementation and rejects a mismatch.
ELF admission additionally requires a nonempty executable PT_LOAD containing
the entry point. A host receipt without this byte-level kernel check is not an
execution grant.

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
