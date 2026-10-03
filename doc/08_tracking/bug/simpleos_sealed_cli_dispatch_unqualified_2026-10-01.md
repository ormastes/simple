# SimpleOS sealed CLI dispatch awaits runtime qualification

Status: OPEN / TEST_BLOCKED. Owner: item1_astra_impl; final reviewer: root.
Requirements: simple_platform_unification REQ-001, REQ-014, REQ-016, REQ-019.

At source baseline `bf28063b843526d1212a760deaed623367a569e5`, inspection sealed
the launch plan but `src/os/cli.spl` called the separate legacy default runner.
The scoped source fix routes that call to `run_os_sealed_v1`; other runner
shapes remain migration work. New command/dispatch functions live in
`src/os/qemu_cli_plan_v1.spl`.

The failing regression was authored before implementation, but could not run:
the isolated checkout has no `bin/release` or `build/bootstrap/stage4`, and no
external admitted Stage 4 runner was supplied. This is blocked red and green
execution, not a proven failure followed by a pass. Docgen, native CLI smoke,
lint and duplication checks remain blocked too.

Unblock: admit a provenance-bound self-hosted Stage 4 binary, execute the
[exact resume plan](../../03_plan/sys_test/simpleos_sealed_cli_dispatch.md),
retain authenticated test and real CLI receipts, and obtain final review.
Retained artifacts are the production source, focused executable regression,
manual draft, host-fixture acceptance work and the resume plan. Never count a
fixture process as a QEMU boot; never count this slice as whole-item completion.
