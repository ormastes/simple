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
