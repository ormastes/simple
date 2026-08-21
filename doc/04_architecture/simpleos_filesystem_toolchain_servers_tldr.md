# SimpleOS filesystem toolchain and servers — TLDR

```text
TCP -> HTTP default|POST /db
VFS read-at -> ELF PT_LOAD -> ring 3
one target Simple payload -> all canonical role paths
```

- One HTTP listener dispatches the bounded DB route; no second scheduler.
- Stream executable ranges; do not whole-buffer Clang.
- No hosted executable cache or global preload substitution.
- Filesystem is hosted policy; GOT is explicit bare-metal only.
- Fake payloads, markers, skips, host work, and stale logs fail closed.
- Wave 4 splits FAT/NVMe/VFS and architecture runtime state into bounded single
  owners; x86_64/AArch64/RV64 server entries consume authenticated execute-open
  authority rather than path-only spawn facades.
- RV64 ELF reads are streamed and bounded; its legacy unauthenticated executor
  is an explicit rejection path.
- Multiarch `simpleos_tool` and LLVM provision receipts prove construction only;
  guest filesystem execution still requires fresh QEMU receipts.
