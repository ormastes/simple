# Agent plan: SimpleOS toolchain deployment image and desktop boot

Date: 2026-08-14
Canonical plan:
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`

| Lane | Scope | Result / owner |
|---|---|---|
| Acceptance/evidence audit | AC-1..AC-12, inventory, blockers, lifecycle | read-only sidecar `acceptance_audit`; merge by root |
| Guide/wiki/traceability audit | guides, expert pages, SSpec/manual and agent plan | read-only sidecar `guide_trace_audit`; merge by root |
| Plan/doc merge | one canonical contract, current inventory, blocker reconciliation | root merge owner |
| Final review | completeness, blocker honesty, guide/manual quality, done/exclusions | separate higher-capability `higher_model_review` |

Frozen interfaces are `simpleos_toolchain_deployment_manifest`,
`simpleos_toolchain_image_admission_receipt`, and
`simpleos_toolchain_desktop_guest_receipt`. Frozen manual helpers are
`step_prepare_toolchain_deployment_image`, `step_boot_simpleos_desktop`, and
`step_compile_and_run_guest_hello`. Setup/checkers are
`prepare_toolchain_deployment_fixture`,
`require_toolchain_deployment_manifest`,
`require_simpleos_desktop_boot_receipt`, and
`require_guest_hello_receipt`. Any incomplete implementation calls `fail(...)`.

Root may merge sidecar findings but cannot self-approve the final plan. The
durable review receipt is
`doc/09_report/review/simpleos_toolchain_deployment_desktop_boot_plan_review_2026-08-14.md`.
No implementation, generated-manual, deployment, desktop, board, verify, or
release PASS is implied by plan completion.
