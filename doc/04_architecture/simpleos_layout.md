# SimpleOS Layout — src/os vs examples/simple_os

**Date:** 2026-04-14

## Intent Per Location

| Path | Role |
|---|---|
| `src/os/` | **Library.** Reusable OS components: drivers, kernel services, compositor, libc shims, port build drivers. Compiled and linked by consumers. |
| `examples/simple_os/` | **Harness.** QEMU-specific integration: boot entries, linker scripts, baremetal weak stubs, memory maps, QEMU device wiring. |

The library does not know about QEMU. The harness does not implement OS logic.

---

## The Boundary Rule

> **Library** (`src/os/`) provides strong `@export("C")` symbols.
> **Harness** (`examples/simple_os/`) provides weak stubs and linker strong-aliases.
> The linker resolves strong over weak — library wins.

### The 65 `spl_handle_*` Wave

The canonical example of this rule in practice:

- `examples/simple_os/` declares 65 `spl_handle_<syscall>` functions as `@weak`
  placeholders that return `ENOSYS`.
- `src/os/kernel/abi/syscall_shim.spl` declares the same 65 names as strong
  `@export("C")` implementations.
- At link time the strong symbols from the library override the weak stubs from
  the harness — no conditional compilation, no `#ifdef`, no manual override list.

This pattern scales: adding a new syscall handler means adding one strong function
in `src/os/`; the harness weak stub is already there waiting.

---

## Overlap Candidates That Are NOT Duplication

Some paths appear in both locations by design:

| Path segment | In `src/os/` | In `examples/simple_os/` | Why both exist |
|---|---|---|---|
| `arch/x86_64/` | Generic x86_64 support code | QEMU-specific memory layout, LAPIC base, etc. | Arch support vs QEMU quirks |
| `boot.spl` | Boot protocol abstraction | `boot_stage1_entry.spl`, `boot_stage2_entry.spl` | Abstract interface vs concrete Limine/multiboot entries |
| `hosted/` | Hosted-mode libc bridge (portable) | Host syscall trampolines specific to Linux/QEMU | Portability layer vs host ABI |
| `apps/` | App framework and shell utilities | QEMU test apps, smoke specs | Reusable apps vs harness-only test runners |

These are not duplicates. Do not merge or flatten them.

---

## When Adding New OS Code

1. **Does it implement OS logic** (a driver, a syscall, a libc function, a kernel
   service, a compositor feature)?
   → Put it in `src/os/`. Export strong symbols.

2. **Is it QEMU-specific wiring** (a boot entry point, a linker script fragment,
   a QEMU device stub, a baremetal memory map)?
   → Put it in `examples/simple_os/`. Use weak symbols where the library will
   provide the real implementation.

3. **Is it a test that exercises the integration** (a QEMU smoke spec, a guest
   binary that calls a syscall)?
   → Put it in `examples/simple_os/apps/` or `test/`.

When in doubt: if the code makes sense outside of QEMU (e.g., on real hardware
or in a hosted environment), it belongs in `src/os/`.

---

## Commit-Review Hint

**Reject PRs that copy files across this boundary.**

Signs of a boundary violation:

- A file from `src/os/` is duplicated under `examples/simple_os/` (or vice versa).
- A strong symbol is defined in the harness directory.
- A weak stub is defined in the library directory.
- A QEMU device address (`0xFEE00000`, etc.) appears in `src/os/`.

Correct fix: move the code to the right side and update `@export`/`@weak`
annotations accordingly.

---

## Related Docs

- [port_dev_chain.md](../02_development/port_dev_chain.md) — toolchain port index
- [bare_metal_integration.md](bare_metal_integration.md) — baremetal runtime notes
- [simpleos_launch_modes.md](simpleos_launch_modes.md) — QEMU launch modes
- [libc_coverage_audit.md](libc_coverage_audit.md) — POSIX surface audit
