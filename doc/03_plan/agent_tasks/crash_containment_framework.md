<!-- codex-design -->
# Agent Tasks — Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

1. Keep the core failure taxonomy aligned across research, requirements, architecture, and code.
2. Maintain `Result` for expected failure and panic-like exit for invariant failure; do not drift toward catchable exceptions.
3. Keep hosted fault-domain defaults and restart policies centralized in [`src/os/crash_policy.spl`](src/os/crash_policy.spl).
4. Extend dashboard worker supervision as the proving-ground path, then lift it into generic launcher/app-host infrastructure.
5. Standardize crash-record fields and logging paths for hosted worker exits.
6. Preserve the resource-default rule:
   interactive/session workloads below `10 GB`, about half available threads; heavy workloads opt in explicitly.
7. Keep bare-metal policy separate and simpler:
   panic/trap/watchdog -> halt or reboot, not hosted restart/quarantine loops.
8. Add and maintain targeted Docker validation for hosted paths plus focused bare-metal panic/watchdog verification.
