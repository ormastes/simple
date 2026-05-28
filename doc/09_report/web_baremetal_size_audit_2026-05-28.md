# Web And Bare-Metal Binary Size Audit

Date: 2026-05-28

## Build Status

| Artifact | Check | Native/ELF Build | Bytes | Dec Section Bytes | Log |
|---|---|---|---:|---:|---|
| Browser smoke | ok | ok | 43208 | 37316 | `build/web_baremetal_size_audit/browser_smoke_native.log` |
| Browser simple render HTML | ok | ok | 22632 | 15882 | `build/web_baremetal_size_audit/simple_render_html_native.log` |
| Simple web static facade | n/a | ok | 18528 | 12651 | `build/web_baremetal_size_audit/simple_web_static_native.log` |
| Simple web script URL facade | n/a | ok | 43160 | 34085 | `build/web_baremetal_size_audit/simple_web_script_native.log` |
| RV32 semihost stdout hello | n/a | ok | 66268 | 8334 | `build/web_baremetal_size_audit/hello_riscv32_semihost.build.log` |

## Source Size Surfaces

| Surface | Files | Lines | Bytes |
|---|---:|---:|---:|
| `examples/browser` | 304 | 75023 | 2850254 |
| `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` | 1 | 15509 | 576503 |

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
| `src/lib/gc_async_mut/web` | 12 | 3784 | 160275 |
| `src/lib/gc_async_mut/gpu/browser_engine` | 10 | 1534 | 58547 |

## Direction

- Browser render size work should first split static render from script/session/network paths.
- The static simple-web facade is measured separately from the script URL facade so script/runtime growth stays visible.
- x86_64 SimpleOS size work should split `baremetal_stubs.c` into boot, serial/stdout, interrupt, GUI, filesystem, network, and crypto/helper lanes.
- Semihost stdout should use the noalloc bare-metal transport library as the shared cross-platform API surface, with only the trap instruction in the platform capsule.
- Set `MAX_BROWSER_EXAMPLE_SOURCE_BYTES`, `MAX_X86_64_BAREMETAL_STUB_SOURCE_BYTES`, or `MAX_RV32_SEMIHOST_ELF_BYTES` to turn this audit into a budget gate.
