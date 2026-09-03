# Full CLI static fast path retains the product link closure

**Status:** open optimization opportunity
**Observed:** 2026-09-03 on macOS arm64

Exact `simple --version` and `simple --help` execute no compiler operation, but
the admitted 24 MiB full CLI still links AppKit, Foundation, CoreServices,
IOKit, SystemConfiguration, Security, CoreFoundation, libc++, and libSystem.
The source-level runtime registry construction has been removed from ordinary
exact static requests, but dynamic-loader and image costs remain inseparable
from the monolithic product closure.

Any fix must preserve the single user-facing executable contract, K1 policy
validation, exact output, global-option behavior, Phase-7 activation, signing,
and plugin admission. Candidate solutions are an entry-closure-erased CLI-0
front executable or equivalent linker dead-stripping; neither should introduce
runtime source interpretation or a Rust-seed fallback.

Acceptance requires a producer-authenticated rebuilt arm64 full CLI and at
least 30 before/after process samples reporting p50, p95, max RSS, binary
segments, linked images, binary digest, and output parity.
