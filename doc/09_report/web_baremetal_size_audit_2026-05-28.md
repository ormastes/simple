# Web And Bare-Metal Binary Size Audit

Date: 2026-05-28

## Build Status

| Artifact | Check | Native/ELF Build | Bytes | Dec Section Bytes | Log |
|---|---|---|---:|---:|---|
| Browser smoke | ok | ok | 34968 | 26189 | `build/web_baremetal_size_audit/browser_smoke_native.log` |
| Browser simple render HTML | ok | ok | 18480 | 7923 | `build/web_baremetal_size_audit/simple_render_html_native.log` |
| Simple web static facade | n/a | ok | 14352 | 4090 | `build/web_baremetal_size_audit/simple_web_static_native.log` |
| Simple web placeholder URL facade | n/a | ok | 14336 | 3889 | `build/web_baremetal_size_audit/simple_web_placeholder_native.log` |
| Simple web file facade | n/a | ok | 14344 | 6335 | `build/web_baremetal_size_audit/simple_web_file_native.log` |
| Simple web script placeholder facade | n/a | ok | 14336 | 3905 | `build/web_baremetal_size_audit/simple_web_script_placeholder_native.log` |
| Simple web script file facade | n/a | ok | 26712 | 16935 | `build/web_baremetal_size_audit/simple_web_script_file_native.log` |
| Bare-metal pure policy probe | ok | ok | 14336 | 6581 | `build/web_baremetal_size_audit/pure_policy_probe_native.log` |
| RV32 semihost stdout hello | n/a | ok | 4892 | 156 | `build/web_baremetal_size_audit/hello_riscv32_semihost.build.log` |
| RV32 semihost trap capsule | n/a | ok | 652 | 48 | `build/web_baremetal_size_audit/riscv32_semihost_trap.build.log` |
| RV64 semihost trap capsule | n/a | ok | 912 | 48 | `build/web_baremetal_size_audit/riscv64_semihost_trap.build.log` |
| ARM semihost trap capsule | n/a | ok | 568 | 20 | `build/web_baremetal_size_audit/arm_semihost_trap.build.log` |
| ARM64 semihost trap capsule | n/a | ok | 704 | 32 | `build/web_baremetal_size_audit/arm64_semihost_trap.build.log` |
| x86_64 minimal boot/stdout capsule | n/a | ok | 1968 | 250 | `build/web_baremetal_size_audit/baremetal_boot_stdout.build.log` |
| ARM64 minimal PL011 startup/stdout capsule | n/a | ok | 1976 | 296 | `build/web_baremetal_size_audit/arm64_baremetal_uart_stdout.build.log` |
| ARM32 minimal PL011 startup/stdout capsule | n/a | ok | 2000 | 332 | `build/web_baremetal_size_audit/arm32_baremetal_uart_stdout.build.log` |
| RV64 minimal 16550 startup/stdout capsule | n/a | ok | 2736 | 178 | `build/web_baremetal_size_audit/rv64_baremetal_uart_stdout.build.log` |
| RV32 minimal 16550 startup/stdout capsule | n/a | ok | 1928 | 178 | `build/web_baremetal_size_audit/rv32_baremetal_uart_stdout.build.log` |
| x86_64 interrupt-control capsule | n/a | ok | 1272 | 33 | `build/web_baremetal_size_audit/baremetal_interrupt_control.build.log` |
| ARM64 interrupt-control capsule | n/a | ok | 592 | 24 | `build/web_baremetal_size_audit/arm64_baremetal_interrupt_control.build.log` |
| ARM32 interrupt-control capsule | n/a | ok | 528 | 24 | `build/web_baremetal_size_audit/arm32_baremetal_interrupt_control.build.log` |
| RV64 interrupt-control capsule | n/a | ok | 736 | 24 | `build/web_baremetal_size_audit/rv64_baremetal_interrupt_control.build.log` |
| RV32 interrupt-control capsule | n/a | ok | 552 | 24 | `build/web_baremetal_size_audit/rv32_baremetal_interrupt_control.build.log` |
| x86_64 startup handoff capsule | n/a | ok | 1936 | 118 | `build/web_baremetal_size_audit/baremetal_startup_handoff.build.log` |
| Shared startup handoff x86_64 capsule | n/a | ok | 1936 | 118 | `build/web_baremetal_size_audit/shared_x86_64_startup_handoff.build.log` |
| Shared startup handoff ARM64 capsule | n/a | ok | 2232 | 164 | `build/web_baremetal_size_audit/shared_arm64_startup_handoff.build.log` |
| Shared startup handoff ARM32 capsule | n/a | ok | 2252 | 180 | `build/web_baremetal_size_audit/shared_arm32_startup_handoff.build.log` |
| Shared startup handoff RV64 capsule | n/a | ok | 2920 | 140 | `build/web_baremetal_size_audit/shared_rv64_startup_handoff.build.log` |
| Shared startup handoff RV32 capsule | n/a | ok | 1976 | 140 | `build/web_baremetal_size_audit/shared_rv32_startup_handoff.build.log` |

## Default Regression Budgets

| Budget | Limit Bytes |
|---|---:|
| Browser smoke native file / dec section | 35200 / 27000 |
| Browser simple render HTML native file / dec section | 19000 / 8500 |
| Browser engine source | 65000 |
| Simple web static facade native file / dec section | 14500 / 5000 |
| Simple web placeholder URL facade native file / dec section | 14500 / 4100 |
| Simple web file facade native file / dec section | 14500 / 6400 |
| Simple web script placeholder facade native file / dec section | 14500 / 4200 |
| Simple web script file facade native file / dec section | 27000 / 17000 |
| Bare-metal pure policy probe native file / dec section | 15000 / 6800 |
| Bare-metal pure policy probe source | 1300 |
| RV32 semihost stdout ELF file / dec section | 6000 / 512 |
| RV32 semihost trap object file / dec section | 768 / 64 |
| RV32 semihost trap source | 1024 |
| RV64 semihost trap object file / dec section | 1024 / 64 |
| RV64 semihost trap source | 1024 |
| ARM semihost trap object file / dec section | 768 / 64 |
| ARM semihost trap source | 1024 |
| ARM64 semihost trap object file / dec section | 768 / 64 |
| ARM64 semihost trap source | 1024 |
| x86_64 minimal boot/stdout object file / dec section | 2300 / 320 |
| x86_64 minimal boot/stdout source | 3000 |
| ARM64 minimal PL011 startup/stdout object file / dec section | 2400 / 360 |
| ARM64 minimal PL011 startup/stdout source | 2600 |
| ARM32 minimal PL011 startup/stdout object file / dec section | 2200 / 340 |
| ARM32 minimal PL011 startup/stdout source | 2800 |
| RV64 minimal 16550 startup/stdout object file / dec section | 2800 / 220 |
| RV64 minimal 16550 startup/stdout source | 2200 |
| RV32 minimal 16550 startup/stdout object file / dec section | 2300 / 260 |
| RV32 minimal 16550 startup/stdout source | 2300 |
| Shared minimal stdout helper source | 2200 |
| x86_64 interrupt-control object file / dec section | 1536 / 64 |
| x86_64 interrupt-control source | 1024 |
| ARM64 interrupt-control object file / dec section | 768 / 64 |
| ARM64 interrupt-control source | 1024 |
| ARM32 interrupt-control object file / dec section | 768 / 64 |
| ARM32 interrupt-control source | 1024 |
| RV64 interrupt-control object file / dec section | 768 / 64 |
| RV64 interrupt-control source | 1024 |
| RV32 interrupt-control object file / dec section | 768 / 64 |
| RV32 interrupt-control source | 1024 |
| x86_64 startup handoff object file / dec section | 2048 / 128 |
| x86_64 startup handoff source | 1024 |
| Shared startup handoff x86_64 object file / dec section | 2048 / 256 |
| Shared startup handoff ARM64 object file / dec section | 2300 / 256 |
| Shared startup handoff ARM32 object file / dec section | 2300 / 256 |
| Shared startup handoff RV64 object file / dec section | 3072 / 256 |
| Shared startup handoff RV32 object file / dec section | 2048 / 256 |
| Shared startup handoff source | 1024 |
| Pure Simple console policy source | 2500 |
| Pure Simple stdout plan source | 2500 |
| Pure Simple stdout policy plan source | 3000 |
| Pure Simple interrupt policy source | 5000 |
| Pure Simple startup policy source | 3000 |
| Pure Simple startup plan source | 2500 |
| Pure Simple semihost policy source | 1500 |
| Pure Simple semihost stdout policy source | 1500 |

## Source Size Surfaces

| Surface | Files | Lines | Bytes |
|---|---:|---:|---:|
| `examples/browser` | 304 | 75035 | 2850509 |
| `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` | 1 | 15509 | 576503 |
| `examples/simple_os/arch/x86_64/boot/baremetal_boot_stdout.c` | 1 | 107 | 2752 |
| `examples/simple_os/arch/arm64/boot/baremetal_uart_stdout.c` | 1 | 57 | 1458 |
| `examples/simple_os/arch/arm32/boot/baremetal_uart_stdout.c` | 1 | 50 | 1375 |
| `examples/simple_os/arch/riscv64/boot/baremetal_uart_stdout.c` | 1 | 40 | 958 |
| `examples/simple_os/arch/riscv32/boot/baremetal_uart_stdout.c` | 1 | 40 | 958 |
| `examples/simple_os/arch/common/baremetal_min_stdout.h` | 1 | 62 | 1719 |
| `examples/simple_os/arch/x86_64/boot/baremetal_interrupt_control.c` | 1 | 27 | 558 |
| `examples/simple_os/arch/arm64/boot/baremetal_interrupt_control.S` | 1 | 23 | 753 |
| `examples/simple_os/arch/arm32/boot/baremetal_interrupt_control.S` | 1 | 25 | 770 |
| `examples/simple_os/arch/riscv64/boot/baremetal_interrupt_control.S` | 1 | 23 | 740 |
| `examples/simple_os/arch/riscv32/boot/baremetal_interrupt_control.S` | 1 | 23 | 740 |
| `examples/simple_os/arch/x86_64/boot/baremetal_startup_handoff.c` | 1 | 1 | 52 |
| `examples/simple_os/arch/common/baremetal_startup_handoff.c` | 1 | 35 | 685 |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv32/semihost_trap.S` | 1 | 30 | 867 |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv/semihost_trap.S` | 1 | 30 | 867 |
| `src/lib/nogc_async_mut_noalloc/baremetal/arm/semihost_trap.S` | 1 | 27 | 786 |
| `src/lib/nogc_async_mut_noalloc/baremetal/arm64/semihost_trap.S` | 1 | 25 | 787 |
| `examples/09_embedded/baremetal/baremetal/pure_policy_probe.spl` | 1 | 29 | 1018 |
| `src/lib/nogc_async_mut_noalloc/baremetal/console_policy.spl` | 1 | 56 | 1870 |
| `src/lib/nogc_async_mut_noalloc/baremetal/stdout_plan.spl` | 1 | 65 | 1999 |
| `src/lib/nogc_async_mut_noalloc/baremetal/stdout_policy_plan.spl` | 1 | 55 | 2129 |
| `src/lib/nogc_async_mut_noalloc/baremetal/interrupt_policy.spl` | 1 | 72 | 3315 |
| `src/lib/nogc_async_mut_noalloc/baremetal/startup_policy.spl` | 1 | 15 | 458 |
| `src/lib/nogc_async_mut_noalloc/baremetal/startup_plan.spl` | 1 | 29 | 1097 |
| `src/lib/nogc_async_mut_noalloc/baremetal/semihost_policy.spl` | 1 | 19 | 658 |
| `src/lib/nogc_async_mut_noalloc/baremetal/semihost_stdout_policy.spl` | 1 | 23 | 739 |

## Browser Cluster Source Sizes

| Cluster | Files | Lines | Bytes |
|---|---:|---:|---:|
| `examples/browser/feature/paint` | 18 | 8234 | 289955 |
| `examples/browser/feature/script` | 23 | 8220 | 294191 |
| `examples/browser/feature/net` | 15 | 6671 | 235625 |
| `examples/browser/feature/parser` | 13 | 6829 | 282009 |
| `examples/browser/feature/layout` | 10 | 4526 | 170086 |
| `examples/browser/feature/dom` | 9 | 4854 | 181376 |
| `examples/browser/feature/style` | 13 | 3914 | 150153 |
| `src/lib/gc_async_mut/web` | 13 | 3928 | 170664 |
| `src/lib/gc_async_mut/gpu/browser_engine` | 17 | 1716 | 62320 |

## Retention Checks

| Artifact | Forbidden Binary Marker Matches | Forbidden Build Log Marker Matches |
|---|---:|---:|
| Browser simple render HTML | n/a | 0 |
| Simple web static facade | 0 | 0 |
| Simple web placeholder URL facade | 0 | 0 |
| Simple web file facade | 0 | 0 |
| Simple web script placeholder facade | 0 | 0 |
| Simple web script file facade expected retention | 0 | 3 |
| Simple web script file facade forbidden full renderer | 0 | 0 |
| Bare-metal pure policy probe | 0 | 0 |
| RV32 semihost trap capsule | 0 | n/a |
| RV64 semihost trap capsule | 0 | n/a |
| ARM semihost trap capsule | 0 | n/a |
| ARM64 semihost trap capsule | 0 | n/a |
| x86_64 minimal boot/stdout capsule | 0 | n/a |
| ARM64 minimal PL011 startup/stdout capsule | 0 | n/a |
| ARM32 minimal PL011 startup/stdout capsule | 0 | n/a |
| RV64 minimal 16550 startup/stdout capsule | 0 | n/a |
| RV32 minimal 16550 startup/stdout capsule | 0 | n/a |
| x86_64 interrupt-control capsule | 0 | n/a |
| ARM64 interrupt-control capsule | 0 | n/a |
| ARM32 interrupt-control capsule | 0 | n/a |
| RV64 interrupt-control capsule | 0 | n/a |
| RV32 interrupt-control capsule | 0 | n/a |
| x86_64 startup handoff capsule | 0 | n/a |
| Shared startup handoff x86_64 capsule | 0 | n/a |
| Shared startup handoff ARM64 capsule | 0 | n/a |
| Shared startup handoff ARM32 capsule | 0 | n/a |
| Shared startup handoff RV64 capsule | 0 | n/a |
| Shared startup handoff RV32 capsule | 0 | n/a |

## Direction

- Browser render size work should first split static render from script/session/network paths.
- `simple_web_html_renderer` is the HTML-only core; URL/file loading, script execution, and corpus fixtures must stay in separate facades.
- The static simple-web facade and about:/unloaded URL facade are measured separately so file, script, and fixture growth stays visible.
- `simple_web_url_placeholder_renderer` is the about:/unloaded URL lane and must not retain file I/O, BrowserRenderer, script execution, or corpus fixtures.
- `simple_web_file_renderer` is the file-capable facade and must not retain the compatibility class, script execution, BrowserRenderer, corpus fixtures, or the ARGB intermediate HTML core.
- `simple_web_script_placeholder_renderer` is the unloaded/about: script-mode lane and must not retain BrowserRenderer, process, file, or script execution code.
- `simple_web_script_renderer` is the explicit file:// script-capable lane; its BrowserRenderer/process/file stub cost is measured separately from static and placeholder facades.
- Corpus fixture compatibility lives in `simple_web_corpus_fixture_renderer`; production static render must not retain PPM baseline loading.
- x86_64 SimpleOS size work should split `baremetal_stubs.c` into boot, serial/stdout, interrupt, GUI, filesystem, network, and crypto/helper lanes.
- `baremetal_boot_stdout.c` is the current x86_64 platform capsule baseline for boot/stdout only; keep it small while moving policy and reusable behavior into pure Simple.
- `arm64/boot/baremetal_uart_stdout.c` is the ARM64 PL011 capsule baseline for startup/stdout only; GIC, PCI, filesystem, network, and GUI stay out of this lane.
- `arm32/boot/baremetal_uart_stdout.c` is the ARM32 PL011 capsule baseline for startup/stdout only; GIC, framebuffer, filesystem, and GUI stay out of this lane.
- `riscv64/boot/baremetal_uart_stdout.c` is the RV64 16550 capsule baseline for startup/stdout only; PLIC, CLINT, virtio, filesystem, and GUI stay out of this lane.
- `riscv32/boot/baremetal_uart_stdout.c` is the RV32 16550 capsule baseline for startup/stdout only; PLIC, CLINT, virtio, filesystem, and GUI stay out of this lane.
- `baremetal_interrupt_control.c` is the x86_64 platform capsule baseline for CLI/STI/HLT and PIC masking only; APIC policy stays in pure Simple until controller code is explicitly imported.
- `arm64/boot/baremetal_interrupt_control.S` is the ARM64 platform capsule baseline for DAIF mask/unmask and WFE only; GIC policy stays in pure Simple until controller code is explicitly imported.
- `arm32/boot/baremetal_interrupt_control.S` is the ARM32 platform capsule baseline for CPSID/CPSIE and WFE only; GIC/NVIC policy stays in pure Simple until controller code is explicitly imported.
- `riscv64/boot/baremetal_interrupt_control.S` is the RV64 platform capsule baseline for mstatus.MIE mask/unmask and WFI only; PLIC/CLINT policy stays in pure Simple until controller code is explicitly imported.
- `riscv32/boot/baremetal_interrupt_control.S` is the RV32 platform capsule baseline for mstatus.MIE mask/unmask and WFI only; PLIC/CLINT policy stays in pure Simple until controller code is explicitly imported.
- `common/baremetal_startup_handoff.c` is the shared multiplatform capsule baseline for module-init and `spl_start` handoff only; stack/hart policy stays in pure Simple.
- `x86_64/boot/baremetal_startup_handoff.c` is a thin compatibility wrapper over the shared startup handoff capsule.
- Semihost stdout should use the noalloc bare-metal transport library as the shared cross-platform API surface, with only the trap instruction in the platform capsule.
- `riscv32/semihost_trap.S` is the RV32 platform capsule baseline for the semihost magic sequence only; stdout operation policy stays in pure Simple.
- `riscv/semihost_trap.S` is the RV64 platform capsule baseline for the semihost magic sequence only; stdout operation policy stays in pure Simple.
- `arm/semihost_trap.S` is the ARM/Thumb platform capsule baseline for the BKPT semihost trap only; stdout operation policy stays in pure Simple.
- `arm64/semihost_trap.S` is the AArch64 platform capsule baseline for the HLT semihost trap only; stdout operation policy stays in pure Simple.
- `baremetal/console_policy.spl` is the pure-Simple policy surface for shared semihost/UART stdout selection.
- `baremetal/semihost_policy.spl` is the pure-Simple policy surface for stdout semihost op selection before importing trap/transport code.
- `baremetal/semihost_stdout_policy.spl` adds null-safety/fd metadata while keeping the opcode policy importable for tiny native probes.
- `baremetal/stdout_plan.spl` combines console and semihost stdout policy before importing syscall, semihost transport, or UART implementations.
- `baremetal/stdout_policy_plan.spl` adds semihost stdout safety metadata while keeping the tiny stdout plan opcode-only.
- `baremetal/interrupt_policy.spl` is the pure-Simple policy surface for interrupt controller selection and vector classification.
- `baremetal/startup_policy.spl` is the pure-Simple policy surface for stack and hart startup defaults before importing architecture startup capsules.
- `baremetal/startup_plan.spl` composes startup defaults with interrupt-controller selection while keeping scalar startup policy importable for tiny native probes.
- `pure_policy_probe.spl` proves examples can import only pure policies without retaining transport or controller implementations.
- The split lanes now have default regression budgets. Set any `MAX_...` environment value higher, lower, or empty to tune a specific gate.
