*Source: `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`*
*Last Updated: 2026-03-12*

---

# Remote Baremetal Runtime Checks

**Feature IDs:** #RBRT-001
**Category:** Tooling
**Difficulty:** 3/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** [doc/plan/baremetal_remote_remaining_checklist_2026-03-08.md](doc/plan/baremetal_remote_remaining_checklist_2026-03-08.md)
**Design:** [doc/design/remote_jit_architecture.md](doc/design/remote_jit_architecture.md)
**Research:** [doc/research/trace32_remote_interfaces_2026-03-08.md](doc/research/trace32_remote_interfaces_2026-03-08.md)

## Overview

Checks the current remote baremetal execution plumbing used by the Simple test
runner. The spec covers:

- composite mode parsing for `interpreter(remote(baremetal(...)))`
- QEMU RISC-V32 remote debug smoke using a temporary ELF plus GDB memory read
- TRACE32 readiness state through `t32rem` discovery and repo-managed config

This spec is intentionally host-aware. It treats missing optional host tools as
`skip:` and host/runtime blockers as `blocked:` so the test captures current
environment state without claiming a full hardware verification that the repo
does not currently provide.

## Syntax

```simple
val spec = "interpreter(remote(baremetal(riscv32)))"
val base = extract_base_runtime(spec)
val layer = extract_platform_layer(spec)
val arch = extract_arch_from_spec(spec)
```

## Examples

```simple
val qemu_status = qemu_riscv32_remote_memory_status()
val t32_status = trace32_remote_status()
expect(status_is_acceptable(t32_status)).to_equal(true)
```
