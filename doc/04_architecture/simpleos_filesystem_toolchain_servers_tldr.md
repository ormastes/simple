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
- Stage 4 low-memory uses an explicit `ModuleSurface` declaration index, then
  parses/lowers one full Module at a time; a body-stripped `Module` is forbidden.
- Only trait defaults and enum field-default expressions retain executable AST
  across the surface pass; source fingerprints and canonical trait origins fail
  closed.
- Streaming requires Stage4 AOT + entry-closure + low-memory +
  `SIMPLE_BOOTSTRAP_STAGE4=1`, and excludes VHDL.
