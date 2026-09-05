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
## Restart12 selected deployment requirements (2026-08-14)

- REQ-SOS-TD-001: only an admitted pure-Simple Stage 4 host CLI may produce the
  strict `x86_64-unknown-simpleos` payload; fallback is disabled and the Rust
  seed is bootstrap-only.
- REQ-SOS-TD-002: `/SYS/SIMPLETOOL.SDN` binds the target payload, genuine
  guest-static `ld.lld`, `/usr/lib/SIMAIN.O`, `/HELLO.SPL`, kernel, and every
  canonical Simple alias; a pre-boot external receipt separately binds the
  final image, and a post-boot desktop/guest receipt binds live evidence to it.
- REQ-SOS-TD-003: one canonical `gui_entry_desktop.spl` OVMF/GRUB run proves
  desktop readiness, scanout/framebuffer evidence, `/usr/bin/simple --version`,
  guest-native compile/link, mounted-filesystem execution, exact `Hello World`,
  and rc=0.
- REQ-SOS-TD-004: the executable/manual interface and fail-closed helper names
  are frozen by
  `doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.
