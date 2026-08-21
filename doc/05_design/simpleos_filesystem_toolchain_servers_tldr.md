# SimpleOS filesystem toolchain and servers design — TLDR

- VFS header/phdr/range reads feed the existing ELF mapper.
- Target stamp + ELF validation gate every role path.
- HTTP asserts two real responses.
- DB asserts create → insert → select of a known value.
- Clang and Simple each prove guest path, version, compile, output, and run.
- Any missing/stale/fake/preloaded/host-only evidence returns nonzero.
- FAT mount state stays with one boot publication owner; NVMe DMA/lease/direct
  I/O owners meet VFS only through bounded shared interfaces.
- Authenticated x86_64/AArch64/RV64 entries wait and collect loader-issued
  tasks; RV64 rolls back streamed-load allocation on every failure.
- Build/provision receipts intentionally set no live execution claim.
