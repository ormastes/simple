<!-- codex-research -->
# macOS native Simple Container NFR options (2026-09-28)

| Option | Target | Pros | Cons | Effort |
|---|---|---|---|---|
| A — fail closed | No launch on missing signature, entitlement, sandbox-state, native identity, deadline, or cleanup evidence; bounded output; single trusted owner. | Matches the current rootless design and prevents false readiness. | Requires a new Mac observation owner and live negative fixtures. | L, integrated with feature option A. |
| B — arbitrary tree | Prove every descendant is tracked across `setsid`/`setpgid` and absent after cancellation, with bounded cleanup time. | Supports arbitrary workload claim if an OS authority exists. | No qualifying rootless macOS primitive identified; likely privileged service. | XL, integrated with feature option B. |
| C — no runtime target | Report Mac launch unavailable and retain static contract checks only. | No misleading performance or isolation claim. | No operational Mac route. | S, integrated with feature option C. |

Recommendation: A with feature option A. Set numeric startup, latency, and RSS
targets only after a real Mac owner and representative fixture can measure them;
do not substitute the Linux observer's numbers.
