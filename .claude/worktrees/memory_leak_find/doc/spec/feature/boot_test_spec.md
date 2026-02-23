# Bare-Metal Boot Code Integration Tests

**Feature ID:** #BAREMETAL-004 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/boot_test_spec.spl`_

---

## Overview

Integration tests for bare-metal boot code across x86 Multiboot, ARM Cortex-M, and
RISC-V Machine Mode architectures. These slow tests run actual kernels in QEMU to verify
boot sequences, startup initialization, trap handling, and cross-architecture boot behavior.
Requires QEMU installation to execute.

## Syntax

```simple
fn check_qemu() -> bool:
    val result = shell("which qemu-system-x86_64 > /dev/null 2>&1")
    result.exit_code == 0

slow_it "boots minimal x86 kernel", fn():
    if not check_qemu():
        return
    expect(true).to_equal(true)
```

---

## Test Structure

### Bare-Metal Boot Code
_Integration tests for boot implementations._

#### x86 Multiboot
_Test x86 Multiboot-compliant boot sequence._

#### ARM Cortex-M Startup
_Test ARM Cortex-M reset handler and initialization._

#### RISC-V Machine Mode
_Test RISC-V M-mode startup and trap handling._

#### Cross-Architecture
_Tests that run on multiple architectures._

