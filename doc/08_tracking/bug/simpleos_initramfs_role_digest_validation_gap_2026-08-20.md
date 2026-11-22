# SimpleOS initramfs role/digest validation gap

Status: open; static module closure implemented, runtime executable verification remains release-blocking

The packer now stages and hashes distinct compiler, interpreter, and loader
roles, emits their exact guest paths and digests in `SYS/SIMPLETOOL.SDN`, and
validates those bindings against the archived payload bytes. The pure-Simple
validator bounds zstd input and output, parses newc structurally, rejects unsafe
paths and unsupported link/file shapes, and fails closed on duplicate, missing,
renamed, or tampered role payloads.

Source closure is implemented by `src/os/port/initramfs_validate.spl` and its
behavioral archive spec. Release evidence is still blocked until the admitted
self-hosted Simple runtime executes that spec and the canonical target-image
and in-guest toolchain gates. Sequence-compressed zstd blocks remain rejected;
the packer emits bounded raw/RLE blocks until an output-capped pure decoder is
available.

The strict module boundary is now explicit. `cpio_newc.spl` exports only
`CpioEntry` and the fail-closed, resource-capped `cpio_parse_bounded` result
surface for structural archive consumers; malformed input never returns a
successfully parsed prefix. `smf.spl` owns
canonical EOF-128 header parsing and exports a narrow `Result`-based admission
facade for explicit SimpleOS executable envelopes. The initramfs validator no
longer imports `SmfHeader`, parses SMF offsets itself, or reads private header
fields. Runtime compilation and execution evidence remains deferred by the
no-runtime constraint of this implementation lane.

---

## Lane disposition 2026-11-22 (simpleos-loader-gaps) — verification-pending

Status: verification-pending (code-level gap closed; QEMU/native evidence outstanding).

- Root cause of "no evidence it runs": release transplant `88aac2ffe28` rewound
  `src/os/port/initramfs_pack.spl` to an older packer that emitted
  `host_payload`/`guest_roles` (and referenced an undefined `simple_binary`)
  while HEAD's validator only accepts `role_bindings:`. The two were mutually
  incompatible. Forward repair: restored the packer, `_initramfs_pack/{archive,support}.spl`,
  validator and spec from `58c57b730c9`; `disk_image_bake.spl` now takes the four
  role artifacts from `SIMPLEOS_{INIT,COMPILER,INTERPRETER,LOADER}_BINARY` and fails closed.
- Validator defects fixed: `_zstd_bounded_le` returned a bare `i64` instead of
  `Ok(value)`; an SMF-trailed artifact was admitted by its ELF stub prefix,
  bypassing SMF role/arch/ABI/stub checks.
- Real load path: `executable_source._initramfs_read_file_bytes_or_empty` now runs
  `initramfs_role_gate_v1` once per decoded archive. A manifest that fails
  role/digest binding refuses the whole archive; an archive with no
  `SYS/SIMPLETOOL.SDN` never serves toolchain role paths. The reader also now
  strips the leading `/` before matching (cpio entries are stored relative, so
  absolute lookups previously never matched a real archive).
- Evidence (interpreter, `bin/simple.exe test`): `initramfs_pack_archive_validation_spec`
  13/20 -> 21/21; new `test/01_unit/os/kernel/loader/initramfs_role_gate_spec.spl` 1/3 -> 3/3.
  `executable_source_spec` (5/8) and `executable_source_vfs_spec` (14/15) failures are
  pre-existing and identical before/after.
- Remaining: no boot-chain caller of `set_initramfs_blob` exists in `src/os` (the riscv64
  DTB parser knows `initrd_start` but does not hand the blob over), so the gated reader is
  the designated kernel path but its blob source is unconnected. Kernel-target build of the
  `os.kernel -> os.port.initramfs_validate` import (and its `std.common.compress.zstd` use)
  is unverified; QEMU was down.
