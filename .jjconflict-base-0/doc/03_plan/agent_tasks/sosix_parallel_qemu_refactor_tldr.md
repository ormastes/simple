# SOSIX/QEMU Parallel Plan — TLDR

```text
freeze contracts -> refactor SOSIX/settings -> six guest lanes
                 -> four host lanes -> integrate -> sabotage -> verify
```

- One `QemuLaneSettingsV1` contract; no copied QEMU argv.
- Large artifacts resolve by env/local config/default; this host uses `/mnt/data/.simple` and others default to `~/.simple`.
- SOSIX splits into typed core, filesystem, compatibility, and evidence owners.
- WM/renderers keep semantic ownership but use async SOSIX host display/input/timer/file/process capabilities.
- Hosts: Linux, Windows, macOS, FreeBSD. Guests: x86/ARM/RISC-V × 32/64.
- Every guest proves boot, mounted-filesystem `ls`, and arbitrary program execution.
- Compiler rows additionally prove target-native Simple version + compile/run.
- TCG is correctness-only; native timing requires retained KVM/HVF/WHPX argv.
- macOS can be handed off but remains blocked, never excluded or passed.
- Shared choke points have one merge owner; sidecars own disjoint new directories.
- Each criterion runs once unchanged, with three repair cycles maximum.
- Completion requires fresh evidence for every required matrix cell.
