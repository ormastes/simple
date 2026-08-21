# Disk Image Bake Specification

The executable spec covers the pure admission/rendering boundary used by the
Phase-2 bake. It does not construct a disk image or initramfs without admitted
target-native artifacts.

## Executable behavioral scenarios

`test/02_integration/os/port/disk_image_bake_spec.spl` exercises:

- pure-Simple SHA-256 output for role payload bytes;
- admission of exactly three explicit, non-empty compiler/interpreter/loader
  artifacts using valid EOF-trailer SMF envelopes;
- typed rejection of missing and empty artifacts;
- rejection of the general `simple`/`simple_simpleos` fallback payload;
- typed rejection of malformed executable bytes before image construction;
- typed rejection of empty, control, quote, backslash, and noncanonical
  artifact paths both at admission and at manifest rendering;
- full public-render revalidation of caller-constructed role, SMF bytes,
  digest, and canonical guest-path bindings;
- pairwise path and digest uniqueness; and
- rendering of canonical guest role paths with artifact paths and digests.

The test imports only the exported pure APIs from
`src/os/port/disk_image_bake.spl`; it does not inspect source or documentation.

## Manual blocked row

**BLOCKED — target-native image construction.** The full bake remains blocked
for x86_64 (`x86_64-unknown-simpleos`), AArch64
(`aarch64-unknown-simpleos`), and RV64GC (`riscv64gc-unknown-simpleos`) until
each row has admitted LLVM/Clang/LLD/sysroot, init, compiler, interpreter, and
loader artifacts plus explicit browser/version evidence. The manual row must
then verify that the same admitted role paths and digests reach FAT32,
`/SYS/SIMPLETOOL.SDN`, and initramfs, followed by a guest filesystem
compile/link/load/run receipt. The blocked work has no executable placeholder.
