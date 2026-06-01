# Pure Simple Profile-Guided Executable Optimization System Test Plan

Date: 2026-06-01

## Scope

Design verification for:
- persistent `.sprof` loader and merge behavior;
- native function/block/edge counters;
- pure-Simple BOLT-like executable layout optimization;
- bare-metal software-breakpoint counter lifecycle;
- overhead protection and breakpoint removal.

## Executable Specs

| Spec | Purpose |
|------|---------|
| `test/system/app/optimize/feature/sprof_loader_spec.spl` | validate/load/merge profile summaries |
| `test/system/app/compile/feature/native_profile_counter_spec.spl` | native counter ABI, disabled-counter behavior, and generated-C function/block/edge/call-path insertion |
| `test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl` | layout planner and rejection rules |
| `test/system/app/compile/feature/native_layout_section_map_spec.spl` | generated-C section-map parsing and compile-path transform contracts |
| `test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl` | patch/trap/count/restore/auto-disarm state machine |
| `test/system/os/baremetal/feature/breakpoint_counter_target_adapter_spec.spl` | x86, ARM/Thumb/AArch64, RISC-V/RVC target adapter resume, QEMU runner planning, and evidence normalization |
| `test/system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl` | per-arch breakpoint probe image planning and serial evidence field contract |

Executable specs must live under `test/`; generated/manual docs mirror under
`doc/06_spec/`.

Current status: the executable contract specs above exist and pass. Production
helper slices exist for `.sprof` text/file loading, native counter metadata and
runtime snapshot import, generated-C function/block/edge/call-path insertion,
executable layout eligibility and manifest planning, generated-C section-map
emission and consumption, and bare-metal breakpoint state/ledger policy. The
QEMU breakpoint bridge now plans host QEMU commands and parses serial evidence
without claiming proof when images or binaries are missing. The breakpoint
probe-image contract now defines per-arch source/output/linker/compiler plans
and required serial evidence fields, but still fails closed until real ELF
artifacts exist. The current executable optimizer slice writes deterministic
Simple-owned layout, native symbol-order, and generated-C section-map artifacts
rather than rewriting arbitrary ELF bytes.

## Requirement Traceability

| Objective Item | Planned Evidence |
|----------------|------------------|
| Persistent profile loader | corrupt/stale/exact profile load tests; startup overhead report |
| Simple native optimize | native O-level plus profile-counter ABI tests |
| Pure Simple BOLT-like optimizer | metadata-only layout planning tests; native symbol-order/C section-map artifact tests; no external BOLT command dependency |
| Generated-C layout consumption | section-map parser/transform tests; fail-closed unused symbol and unsafe section tests |
| Native counter feature | function/block/edge/call-path counter contract tests; generated-C insertion checks for all four counter classes |
| Bare-metal counter impl | breakpoint site table and patch ledger tests |
| Bare-metal probe images | per-arch source/output/linker/compiler/QEMU plan tests; serial evidence field contract tests; generated C source/linker artifact tests for patch/restore/rearm/cleanup/icache/serial evidence; all-arch staging idempotence; live RV32/RVC32/RV64/RVC64 QEMU serial capture evidence |
| Prevent slow breakpoint overhead | auto-disarm and sampled-only fallback tests |
| Analyze call path | bounded call-path hash and promotion tests |
| Remove breakpoint when profiled | cleanup-on-stop/panic/watchdog tests |

## Pass Criteria

- Profile loader never performs hot-path file I/O.
- Disabled native counters do not change non-profile builds.
- Layout optimizer preserves entry, symbols, relocations, and manifest mapping.
- Bare-metal breakpoint counters restore original instructions in every exit
  path.
- Hot loop breakpoints are removed or downgraded after calibration.
- Every speedup claim has before/after workload evidence.

## Verification Commands

Baseline documentation gates:

```bash
git diff --check
find doc/06_spec -name '*_spec.spl' | wc -l
```

Initial code-slice gates:

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/app/optimize
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/app/compile
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check test/system/app/optimize/feature/sprof_loader_spec.spl test/system/app/compile/feature/native_profile_counter_spec.spl test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/app/optimize/feature/sprof_loader_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/app/compile/feature/native_profile_counter_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/app/compile/feature/native_layout_section_map_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/app/optimize/feature/profile_layout_cli_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/os/baremetal/feature/breakpoint_counter_target_adapter_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean
```

Native executable slices add:

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/compiler
cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
```

Bare-metal slices add QEMU smoke and explicit hardware-unavailable records when
real hardware is not present. The next live-evidence gate must provide per-arch
images that emit `simple-breakpoint-evidence;...` serial lines and then run
those images through `breakpoint_qemu_run_serial_evidence`.

## Manual Review Policy

Generated specs must read as operator manuals:
- show how a profile is loaded and rejected;
- show how counters are enabled and disabled;
- show how the executable layout manifest maps original to optimized offsets;
- show how breakpoint counters are armed, auto-disarmed, and cleaned up.
