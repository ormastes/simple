# Pure Simple Profile-Guided Executable Optimization Requirements

Date: 2026-06-01

Selection: full MDSOC+ profile optimization capsule from the accepted SPipe
state: persistent `.sprof` profile loading, native profile counters,
pure-Simple executable layout planning, and bare-metal breakpoint profiling.

## Functional Requirements

- REQ-001: Native profile-counter builds must write durable
  `<output>.simple-profile-counters` sidecar metadata.
- REQ-002: Native counter metadata plus observed counter snapshots must write a
  reloadable `.sprof` profile file.
- REQ-003: The optimize layout bridge must consume executable metadata and a
  reloadable `.sprof` profile to write a deterministic layout manifest.
- REQ-004: The executable layout planner must preserve manifest validity,
  separate hot and cold functions deterministically, and reject unsafe layout
  transforms.
- REQ-005: The layout path must not invoke external BOLT, `llvm-bolt`, or
  `perf2bolt`.
- REQ-006: Bare-metal breakpoint profiling must model patch, trap, count,
  restore, rearm, cleanup, invalid patch, missing icache flush, and sampled-only
  fallback behavior.
- REQ-007: SPipe executable specs must live under `test/`, generated/manual
  scenario docs must live under `doc/06_spec/`, and no executable `.spl` specs
  may be placed under `doc/06_spec/`.
- REQ-008: The feature must provide restartable documentation covering the
  implementation, verification evidence, and any explicit scope exclusions.

## Scope Exclusions

- Arbitrary ELF rewriting outside Simple-owned settlement/native metadata.
- Hardware-only bare-metal speedup claims without QEMU or hardware evidence.
- Full release automation unless explicitly requested after verification.
