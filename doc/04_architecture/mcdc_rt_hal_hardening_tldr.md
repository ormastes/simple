<!-- codex-architecture -->
# MC/DC, RT, and HAL Hardening — TLDR

Pure Simple owns the feature. HIR describes decision identity/masking; MIR emits
internal decision/condition probes and expands them before backends. Static-off
omits the route, static-on calls owner-local preallocated storage, and dynamic
mode publishes a validated capsule at a quiescent boundary with a branch-only
dormant path.

The parent test runner consumes bounded versioned evidence and applies exact
normal+ MC/DC gating. Reasoned scenario omissions and decision exclusions remain
separate. RT/HAL executes Pure once, then compares C/Rust through exact 256-bit
receipts in a bounded process arena; typed environment plans own host access.

RT defaults to staged critical admission and rejects unproved hot-path effects.
Recoverable unwind has a bounded POSIX ELF x86-64/AArch64/RV64 source ABI and
fails closed elsewhere. All of this remains unverified pending an admitted
self-hosted Stage 3/4 runtime and same-fixture timing/RSS/allocation evidence.

Start with `src/compiler/50.mir/`, `src/lib/nogc_sync_mut/mcdc/`,
`src/lib/nogc_sync_mut/rt_hal/`, `src/lib/common/env_access/`, and
`test/05_perf/mcdc_rt_hal/`.

Formal masking contexts are compiler-fingerprinted and cold-derived with a
64-requirement context cap. Tagged RT/HAL returns write fixed owner receipt
rings; processes and comparison run only during cold drain/finalization.
Hardware probes use a sealed typed registry, and pinned real C/Rust fixtures
exercise the scalar protocol without displacing Pure ownership. Unverified.
