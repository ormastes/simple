# macOS SimpleOS guest container implementation lanes

**Superseded 2026-09-27:** The user selected native execution on each OS and
excluded VMs from Simple Container. Follow
[native_macos_simple_container.md](native_macos_simple_container.md). The
QEMU/guest lanes below are historical and are not active tasks.

**Current owner:** Codex. **Final reviewer:** Astra or equivalent high-capability
review. **Merge owner:** Codex after verification PASS. Sidecar lanes: N/A for
this local value-contract slice. Astra reviewed the route before this slice.

| Order | Lane | Deliverable | Acceptance |
|---|---|---|---|
| 1 | Common contract | Attempt and observation binding in `.spl` | Focused spec executes and passes on self-hosted runtime. Source written; execution inconclusive because test child exited early. |
| 2 | Guest service | Bounded dispatcher over existing SimpleOS provider | Source-only dispatcher and focused spec drafted; real managed task ID and kernel exit still require authenticated loader repair and executable evidence. |
| 3 | Host VM | QEMU/HVF boot, image check, private channel, deadline and teardown | Fresh guest boot and request/receipt round trip on macOS. |
| 4 | Orchestration | Explicit VM class, SimpleOS execution OS, macOS physical host | Pod/Job positive path and mismatched-host denial. |
| 5 | Verify | Live fixture and release evidence | STATUS: PASS for focused tests, VM run, cleanup, and provenance. |

The current machine has QEMU executables, but no located SimpleOS boot image.
Its OrbStack service was stopped and the managed workspace could not open the
Docker socket; that Linux guest is not evidence for this SimpleOS route.

The macOS preflight adapter `scripts/check/check-macos-simpleos-container-host.shs`
now emits a bounded SDN host/image identity receipt. Its 2026-09-27 run found
QEMU aarch64 and HVF but no pinned guest image, so it returned `BLOCKED` and
saved `build/handoff/macos-simpleos-container-host-2026-09-27.sdn`. A later
`PREFLIGHT_ONLY` result will still need the guest dispatcher, real kernel task
exit and VM teardown before this lane can pass.
