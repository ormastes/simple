<!-- codex-research -->
# macOS native Simple Container scope decision (2026-09-28)

The existing requirements select native macOS execution without a VM. New
research shows the current Mac process-observation V3/V4 owners are unavailable,
and App Sandbox plus launchd process-group cleanup cannot prove containment of
arbitrary detached descendants. Keep the current `REQ-NMC-001–005` contract
until the user selects a revised executable scope.

| Option | Scope | Pros | Cons | Effort |
|---|---|---|---|---|
| A — trusted signed apps | Independently launch one signed, sandboxed macOS app for one trusted owner; admit only declared cooperative single-process workloads. | Native and unprivileged; aligns with App Sandbox. | Cannot claim arbitrary-program containment or workspace-only filesystem; needs new Mac process observation and live host evidence. | L, roughly 6–10 files plus fixtures. |
| B — arbitrary programs | Add a privileged, explicitly authorized macOS containment service with exact descendant authority, then admit untrusted programs only after adversarial qualification. | Targets the Docker-like workload scope. | Requires administrator installation and likely Apple-controlled Endpoint Security entitlement; breaks the requested rootless property and may still need another enforcement primitive. | XL, more than 12 files plus deployment. |
| C — blocked Mac launch | Keep macOS admission/readiness unavailable until an OS-supported rootless exact-tree primitive is proven. | Honest isolation and cleanup claims. | No working macOS native container now. | S, docs and gates only. |

Recommendation: A for a useful native Mac subset, with `launch_capable=false`
until an unrestricted-host App Sandbox test and exact-owner lifecycle checks
pass. Keep untrusted arbitrary programs rejected. B needs an explicit change
to the no-admin requirement.
