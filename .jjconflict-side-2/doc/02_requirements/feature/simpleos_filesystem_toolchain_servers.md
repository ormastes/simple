# Requirements: SimpleOS filesystem toolchain and servers

The user request directly selects these outcomes; no option document is pending.

- REQ-001: A current-source SimpleOS guest shall answer a real HTTP health and
  document request through the canonical QEMU network gate.
- REQ-002: A SimpleOS guest DB service shall accept a real create, write, and
  read query flow and return the inserted value.
- REQ-003: The target-native `/usr/bin/clang` shall execute from the mounted
  filesystem, compile a guest C source, and the produced ELF shall execute.
- REQ-004: One target-native Simple payload shall be installed at every
  canonical compiler/interpreter/loader path plus `/SYS/SIMPLETOOL.SDN`.
- REQ-005: `/usr/bin/simple --version` and in-guest Simple hello compile/run
  shall execute using mounted guest files.
- REQ-006: Hosted SimpleOS shall resolve executable bytes from filesystem/VFS;
  GOT residency is restricted to explicit bare-metal launch metadata.
- REQ-007: Marker apps, fixed command responses, boot-preloaded substitution,
  host compiles, skipped scenarios, and fake payloads shall fail verification.

