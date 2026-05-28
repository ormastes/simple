# Web And Bare-Metal Binary Size Audit

Date: 2026-05-28

## Build Status

| Artifact | Check | Native/ELF Build | Bytes | Dec Section Bytes | Log |
|---|---|---|---:|---:|---|
| Browser smoke | ok | ok | 34968 | 28451 | `build/web_baremetal_size_audit/browser_smoke_native.log` |
| Browser simple render HTML | ok | ok | 18480 | 8165 | `build/web_baremetal_size_audit/simple_render_html_native.log` |
| Simple web static facade | n/a | ok | 14352 | 4696 | `build/web_baremetal_size_audit/simple_web_static_native.log` |
| Simple web script URL facade | n/a | ok | 34904 | 25005 | `build/web_baremetal_size_audit/simple_web_script_native.log` |
| Bare-metal pure policy probe | ok | ok | 14336 | 5967 | `build/web_baremetal_size_audit/pure_policy_probe_native.log` |
| RV32 semihost stdout hello | n/a | ok | 66268 | 8334 | `build/web_baremetal_size_audit/hello_riscv32_semihost.build.log` |
| x86_64 minimal boot/stdout capsule | n/a | ok | 2840 | 409 | `build/web_baremetal_size_audit/baremetal_boot_stdout.build.log` |

## Default Regression Budgets

| Budget | Limit Bytes |
|---|---:|
| Browser smoke native file / dec section | 36000 / 30000 |
| Browser simple render HTML native file / dec section | 20000 / 10000 |
| Simple web static facade native file / dec section | 19000 / 7500 |
| Simple web script URL facade native file / dec section | 35500 / 26000 |
| Bare-metal pure policy probe native file / dec section | 15000 / 6500 |
| Bare-metal pure policy probe source | 1300 |
| RV32 semihost stdout ELF file / dec section | 70000 / 9000 |
| x86_64 minimal boot/stdout object file / dec section | 4096 / 512 |
| x86_64 minimal boot/stdout source | 4096 |
| Pure Simple console policy source | 2500 |
| Pure Simple interrupt policy source | 5000 |
| Pure Simple startup policy source | 3000 |

## Source Size Surfaces

| Surface | Files | Lines | Bytes |
|---|---:|---:|---:|
| `examples/browser` | 304 | 75035 | 2850509 |
| `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` | 1 | 15509 | 576503 |
| `examples/simple_os/arch/x86_64/boot/baremetal_boot_stdout.c` | 1 | 126 | 2982 |
| `examples/09_embedded/baremetal/baremetal/pure_policy_probe.spl` | 1 | 30 | 1108 |
| `src/lib/nogc_async_mut_noalloc/baremetal/console_policy.spl` | 1 | 56 | 1870 |
| `src/lib/nogc_async_mut_noalloc/baremetal/interrupt_policy.spl` | 1 | 72 | 3315 |
| `src/lib/nogc_async_mut_noalloc/baremetal/startup_policy.spl` | 1 | 15 | 458 |

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
| `src/lib/gc_async_mut/gpu/browser_engine` | 12 | 1555 | 59357 |

## Retention Checks

| Artifact | Forbidden Binary Marker Matches | Forbidden Build Log Marker Matches |
|---|---:|---:|
| Browser simple render HTML | n/a | 0 |
| Simple web static facade | 0 | 0 |
| Bare-metal pure policy probe | 0 | 0 |

## Direction

- Browser render size work should first split static render from script/session/network paths.
- `simple_web_html_renderer` is the HTML-only core; URL/file loading, script execution, and corpus fixtures must stay in separate facades.
- The static simple-web facade is measured separately from the script URL facade so script/runtime growth stays visible.
- Corpus fixture compatibility lives in `simple_web_corpus_fixture_renderer`; production static render must not retain PPM baseline loading.
- x86_64 SimpleOS size work should split `baremetal_stubs.c` into boot, serial/stdout, interrupt, GUI, filesystem, network, and crypto/helper lanes.
- `baremetal_boot_stdout.c` is the current x86_64 platform capsule baseline for boot/stdout only; keep it small while moving policy and reusable behavior into pure Simple.
- Semihost stdout should use the noalloc bare-metal transport library as the shared cross-platform API surface, with only the trap instruction in the platform capsule.
- `baremetal/console_policy.spl` is the pure-Simple policy surface for shared semihost/UART stdout selection.
- `baremetal/interrupt_policy.spl` is the pure-Simple policy surface for interrupt controller selection and vector classification.
- `baremetal/startup_policy.spl` is the pure-Simple policy surface for stack and hart startup defaults before importing architecture startup capsules.
- `pure_policy_probe.spl` proves examples can import only pure policies without retaining transport or controller implementations.
- The split lanes now have default regression budgets. Set any `MAX_...` environment value higher, lower, or empty to tune a specific gate.
