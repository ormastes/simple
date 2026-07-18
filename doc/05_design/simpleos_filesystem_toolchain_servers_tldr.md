# SimpleOS filesystem toolchain and servers design — TLDR

- VFS header/phdr/range reads feed the existing ELF mapper.
- Target stamp + ELF validation gate every role path.
- HTTP asserts two real responses.
- DB asserts create → insert → select of a known value.
- Clang and Simple each prove guest path, version, compile, output, and run.
- Any missing/stale/fake/preloaded/host-only evidence returns nonzero.
