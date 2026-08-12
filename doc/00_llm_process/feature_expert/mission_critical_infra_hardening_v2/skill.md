# Feature Expert: Mission-Critical Infrastructure Hardening V2

Use this expert for the selected compiler/SimpleOS/rendering/bounded-allocation
umbrella lane. Read the feature/NFR requirements, architecture, detail design,
system-test plan, and operator guide before editing.

Preserve these invariants:

- exact-current `PureSimple` compiler evidence only;
- selected SimpleOS subsets are scoped claims, never all-platform claims;
- every DrawIR-v3 plan is bound to one arena and generation;
- active rendering generations cannot grow or silently truncate;
- relaxed allocation is sealed, domain-local, quota-bounded, transactional,
  and forbidden in critical contexts;
- process kill/wait paths reject `pid <= 0` before owner-facade calls;
- missing, stale, skipped, synthetic, cached-only, or external-host-unavailable
  evidence blocks the applicable claim.

Do not edit another session's conflicted files or promote the Rust bootstrap
seed into release evidence. Focused tests are currently blocked by the
`runtime_compiler.spl` merge conflict until its owner resolves it.
