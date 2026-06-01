<!-- codex-architecture -->
# Pure Simple Profile-Guided Executable Optimization Architecture

Date: 2026-06-01

## Goal

Build an MDSOC+ optimization capsule that uses Simple-owned profile data to
optimize interpreter/JIT planning, loader/startup, native executable layout, and
bare-metal call paths without depending on external BOLT.

## MDSOC+ Capsules

| Capsule | Boundary | Responsibility |
|---------|----------|----------------|
| Profile Store | `src/app/optimize`, future shared SMF/profile common layer | `.sprof` validate, load, merge, migrate |
| Native Counter | native build/runtime boundary | function, edge, block, call-path counters |
| Executable Layout | optimize app + settlement/native metadata | pure-Simple BOLT-like reorder/alignment/cold split |
| Bare-Metal Counter | OS/debug/bare-metal capsule | software-breakpoint counters, auto-disarm, sampling fallback |
| Verification | SPipe + reports | overhead, correctness, reproducibility, hardware evidence |

## Architecture-Specific Breakpoint Capsule

The bare-metal counter capsule now separates the architecture contract from
target execution. `src/os/baremetal/profile/breakpoint_counter.spl` owns the
portable profile session state machine and the architecture patch profile:

| Family | Variants | Trap | Width | PC advance | I-cache |
|--------|----------|------|-------|------------|---------|
| x86 | `x86`, `i386`, `x86_64` | `int3` / `0xcc` | 1 | 1 | no explicit target flush |
| ARM | `arm`, `arm32` | ARM `bkpt` / `0xe1200070` | 4 | 4 | required |
| Thumb | `thumb`, `thumb2` | Thumb `bkpt` / `0xbe00` | 2 | 2 | required |
| AArch64 | `aarch64` | `brk #0` / `0xd4200000` | 4 | 4 | required |
| RISC-V | `riscv32`, `riscv64` | `ebreak` / `0x00100073` | 4 | 4 | required (`fence.i`) |
| RVC | `riscv32c`, `riscv64c` | `c.ebreak` / `0x9002` | 2 | 2 | required (`fence.i`) |

The target-backed implementation must provide hooks for reading original
instructions, writing trap instructions, dispatching traps, restoring original
instructions, single-step or PC-advance behavior, rearming, and cleanup. ARM,
Thumb, AArch64, and RISC-V additionally require instruction-cache maintenance
before a site can be considered armed.

Real QEMU/hardware runners belong in target capsules below
`src/os/baremetal/profile/` rather than in the portable counter model:

- `breakpoint_counter_x86.spl`: x86/i386/x86_64 INT3 frame normalization.
- `breakpoint_counter_arm.spl`: ARM/Thumb/AArch64 BKPT/BRK syndrome and PC
  handling plus cache maintenance.
- `breakpoint_counter_riscv.spl`: RV32/RV64/RVC EBREAK cause handling,
  compressed-instruction width detection, and `fence.i`.
- `breakpoint_counter_qemu.spl`: QEMU evidence normalization for all supported
  target families.

Current adapter slice:
- x86 normalizes the INT3 reported PC back to the patched address and records
  the post-single-step resume PC.
- ARM, Thumb, and AArch64 normalize exception PCs at the breakpoint
  instruction and require icache maintenance.
- RISC-V normalizes `mepc`/`sepc` at the EBREAK instruction, accounts for
  2-byte compressed EBREAK, and requires `fence.i`.
- QEMU evidence normalization validates arch, command, patched address,
  original/trap bytes, hit count, trap latency, restore, rearm, cleanup, and
  icache evidence. It fails closed for unsupported arch, trap-byte mismatch,
  missing hits, missing restore, incomplete cleanup, or missing icache flush.
- QEMU runner bridging now maps supported target families to QEMU binaries and
  command arguments, probes host availability, runs a supplied image when
  present, and parses `simple-breakpoint-evidence;...` serial output into the
  same fail-closed validator. Missing image, missing QEMU, and missing serial
  evidence are explicit non-proof statuses.

## Data Flow

```
instrumented interpreter/native/bare-metal run
    -> counters
    -> native snapshot import when using native counters
    -> .sprof merge
    -> profile validation/migration
    -> optimizer plan
    -> native/executable layout transform
    -> verified executable
```

Native profile builds emit metadata sidecars and runtime counter snapshots only
behind the explicit profile-counter path. Normal native builds remain clean by
audit. Snapshot import is fail-closed: missing headers, duplicate slots, missing
slot values, metadata/count mismatches, and missing output paths prevent `.sprof`
write planning.

The generated-C profile build path now derives and inserts four native counter
classes in Simple-owned code: function-entry counters, entry basic-block
counters, return-edge counters, and bounded direct-call path counters. These
sites are emitted only after `--simple-profile-counters` selects the profile
build path; non-profile builds continue to reject leaked counter artifacts in
the build audit.

## Pure-Simple BOLT-Like Optimizer

The optimizer does not invoke BOLT. It consumes `.sprof` and Simple executable
metadata to perform:

1. hot function clustering;
2. hot fallthrough block ordering;
3. cold block/function separation when relocations allow it;
4. branch target locality ranking;
5. alignment hints for hottest entries;
6. reproducibility checks against symbol/relocation tables.

Initial target: Simple settlement/native metadata, not arbitrary ELF rewriting.
The production artifact path is Simple/C-owned: the optimizer emits the
offset manifest, native symbol-order text, and a generated-C section map header
from the same validated plan. Rust linker code is treated as seed/runtime
infrastructure, not the feature implementation surface.

The native compile integration consumes the generated-C section map through
`llvm_direct.spl --simple-layout-section-map=PATH`. The compile path reads the
Simple-emitted header, validates that all section directives target
`.text.simple.*`, injects the corresponding attributes into generated C, and
fails closed when a requested symbol is not present. This keeps layout
optimization in the Simple/C boundary while still allowing the platform C
toolchain to place functions into optimizer-selected text sections.

## Bare-Metal Breakpoint Counter Policy

Software-breakpoint counters are allowed only under a profiling session:

```
candidate site -> patch breakpoint -> trap -> increment -> restore/single-step
               -> rearm if below budget
               -> disarm and mark sampled-only if over budget
```

Rules:
- never arm breakpoints in known hot loops after the calibration window;
- cap hits per site and total traps per time window;
- remove all breakpoints before optimized/release execution;
- persist only counts and confidence into `.sprof`;
- use timer or hardware counters when breakpoint trap cost is too high.
- do not report an architecture as target-backed until QEMU evidence proves
  patch, trap, count, restore, PC advance or single-step, rearm, cleanup, and
  required icache flush behavior for that architecture family.

## Loader Strategy

Profile loading is opt-in. Startup loads at most a validated summary keyed by
module identity, schema version, workload label, and executable build ID. The
loader must not scan the repository or reread `.sprof` during hot execution.

## Safety Gates

- Profile evidence never replaces typed-MIR, safe-deopt, semantic proof, or
  relocation validation.
- Executable layout transforms must be reversible or produce a manifest that
  can prove the original-to-optimized mapping.
- Bare-metal breakpoint sessions must have cleanup on normal exit, panic, and
  watchdog timeout.
