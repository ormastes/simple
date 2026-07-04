<!-- codex-research -->
# SimpleOS SMF App Runtime Local Research

Date: 2026-04-20

## Scope

This research covers the remaining SimpleOS app-runtime work when file I/O and
scheduling are owned by another agent:

- IPC/window protocol
- Filesystem namespace
- Dynamic library loading
- SMF loader harmony
- SMF as both executable package and library package

## Existing Code

### SMF writer and format

- `src/compiler/80.driver/smf_writer.spl` already supports SMF v1.1 trailer
  headers, executable flags, template sections, dependency notes, relocation
  sections, and an embedded-ELF mode.
- `src/compiler/70.backend/linker/smf_header.spl` defines the canonical 128-byte
  `SmfHeader`, including `SMF_FLAG_EXECUTABLE`, `SMF_FLAG_PIC`,
  `SMF_FLAG_HAS_STUB`, `stub_size`, `smf_data_offset`, app type, window size,
  and prefetch hints.
- `src/compiler/70.backend/linker/lib_smf.spl` defines an LSMF archive format
  for bundling multiple SMF modules with an index.
- `src/compiler/70.backend/linker/smf_getter.spl` provides a unified lookup API
  for single `.smf` files and `.lsm` libraries.

### Loader split

- `src/compiler/99.loader/loader/module_loader_lib_support.spl` supports loading
  SMF modules from libraries, caching loaded modules, and using `SmfGetter`.
- `src/compiler/70.backend/linker/smf_reader_memory.spl` can parse in-memory SMF
  bytes and extract embedded ELF objects or relocation sections.
- Risk: `smf_reader_memory.spl` currently parses the header from the first 128
  bytes, while `smf_writer.spl` describes and writes v1.1 headers as EOF trailers.
  This must be harmonized before using SMF as a kernel app package format.

### Existing app executable path

- `src/os/services/vfs/vfs_init.spl` now proves that FAT32-backed executable bytes
  can be read from `/sys/apps/browser_demo`.
- `src/os/kernel/loader/executable_source.spl` currently resolves app paths to
  byte arrays through initramfs, synthetic tests, and VFS fallbacks.
- `src/os/kernel/loader/elf_loader.spl`, `elf64.spl`, and
  `process_image.spl` already model ELF validation and load-plan/image building.

### IPC and window protocol

- `src/lib/common/window_protocol/window_protocol.spl` has shared typed request
  and event structures: create, close, resize, move, focus, keyboard, and mouse.
- The current desktop E2E still uses resident fallback for app launch because
  syscall 13 is deferred. The window protocol exists but is not yet the only
  process-to-WM path.

### Namespace and VFS

- `src/os/services/vfs/vfs.spl` has a VFS manager and mount table abstraction.
- `VfsManager.write/read/close/seek` currently route handles to the first mount;
  a production namespace needs fd-to-mount ownership and per-process roots/cwd.
- `src/os/services/vfs/vfs_init.spl` has root FAT32 aliases for known app files.
  This is good for bootstrapping, but namespace policy must move into process
  metadata and app manifest data.

## Local Conclusion

SMF as executable and library is a good direction if SMF is treated as a package
container and metadata envelope, not as a competing process image format at
first. The kernel loader should initially extract an embedded ELF executable from
an SMF app package and pass it to the existing ELF loader. Dynamic libraries can
use SMF/LSMF metadata and relocation sections, but the runtime linker should only
support PIC libraries with explicit imports/exports in the first production cut.

