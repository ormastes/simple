# Callback field dispatch and indirect return owner loss

Status: OPEN. Canonical bug ID: `runner_callback_field_owner_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/2980

Original failure: C35 full runner: HIR251 PASS, MIR20 errors including callback fields; initial workaround ARM exit14 exposed record field owner loss.

Workaround commits:

- `a2a52f8b836d0ec453aa3b4f527555d5d8f4d9f3`; recovery parent `ea9224a83a64cd20e21d013cf1c2652f891999c4` (review only).
- `83ec8208a4ebe8dd0330cdf72907c23528c6c803`; recovery parent `a2a52f8b836d0ec453aa3b4f527555d5d8f4d9f3` (review only).
- `1de4827be3b6e3d86c101d9d0214b850f3feb932`; recovery parent `83ec8208a4ebe8dd0330cdf72907c23528c6c803` (review only).

Current qualification: C35 narrow fixture ARM runtime PASS with10effects; RISC-V ELF243 object PASS, not execution. Actual C36 env_access_host and rt_hal_isolated_host consumer MIR still FAIL on unresolved callback fields. No runner qualification.

Producer: `96d356291fb75d4d81ff72df901fe3328e9e4bbabd4f4e5317382766b7261c4c`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c35-callback-field-workaround/{arm-final,rv-final-monitor-3002}/; /home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-consumer-fixes/`.

Reproducing/prevention source: `test/fixtures/compiler/callback_field_explicit_call/main.spl`.

Background fix owner and removal condition: Permanent method-field layout and indirect-call return provenance owner; reviewed compiler pair273368/e2b959 remains separate. Remove only after original dot-field calls and aggregate returns pass actual consumers and fixtures on admitted replacement producer.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: a2a52f8b836d0ec453aa3b4f527555d5d8f4d9f3 -> ff6ddda35330aac9da65c717d61bf5254102577d (stable patch-id equal; both UNLANDED on checked release); 83ec8208a4ebe8dd0330cdf72907c23528c6c803 -> da6ef256e3a660a3a12861c0a3685da2e97bc4ad (stable patch-id equal; both UNLANDED on checked release); 1de4827be3b6e3d86c101d9d0214b850f3feb932 -> 0f23b123e0817c1b3a7c0694e5dc5608e3d45407 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Narrow ARM/RISC-V fixture source 1de4827be3b6e3d86c101d9d0214b850f3feb932; actual C36 consumer integrationf7fdaf remains failing.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.

Additional consumer workaround: Additional source workaround 64b8854eaa6eee9470470ddbcef5fa2165902d13 (recovery parent f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c) replaces 11 remaining actual process_task_arena callback calls and retains 7 typed host locals. Source reviewed; changed-consumer native qualification PENDING. This is UNLANDED as of release 95c12f073ffefa99ac774264beeedd68a47e7676 and does not extend prior narrow fixture PASS. Source link https://github.com/ormastes/simple/commit/64b8854eaa6eee9470470ddbcef5fa2165902d13.
