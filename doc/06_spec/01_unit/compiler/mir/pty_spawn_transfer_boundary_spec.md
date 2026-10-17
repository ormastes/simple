# PTY spawn transfer boundary

**Status: TEST_BLOCKED — authored manual; execution and generated docgen pending.**

Source fix status: **fixed in source only**. No scenario below is an execution
PASS, and this manual is not a native compiler admission receipt.

Requirement: `REQ-SMUX-WINDOWS-PTY-SPAWN-OWNER`.
Bug: `BUG-PTY-SPAWN-THREAD-TRANSFER-2026-10-16`.

- Executable spec: [pty_spawn_transfer_boundary_spec.spl](../../../../../test/01_unit/compiler/mir/pty_spawn_transfer_boundary_spec.spl).
- Root cause, retained diagnostic, and pending native fixture commands:
  [bug report](../../../../08_tracking/bug/pty_spawn_misclassified_thread_transfer_2026-10-16.md).
- Compiler owner: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`.

The resolved declaration owner distinguishes `std.sys.pty.spawn` from a task
or actor spawn. The local import alias is not ownership authority. Existing
owner normalization recognizes the public dotted name, canonical library name,
physical source leaf, and Windows absolute leaf path without changing configured
variant selection. Real transfer operations remain explicit and unsupported
native transfer lowering continues to fail closed.

| Scenario | Action | Required assertion | Evidence |
|---|---|---|---|
| Aliased public PTY spawn | Lower the resolved `pty_spawn` alias with handle and command arguments | Ordinary `Call`, no MIR error, no `TransferOut` | TEST_BLOCKED |
| Physical declaration owners | Lower `lib.sys.pty`, source leaf, and Windows absolute owner spellings | Ordinary `Call`, no MIR error, no `TransferOut` for each | TEST_BLOCKED |
| Actor spawn owner | Lower `std.nogc_async_mut.actor.spawn` using its physical `spawn` name | Exactly two existing Thread `TransferOut` facts remain | TEST_BLOCKED |
| Actor and legacy builtin spellings | Lower `spawn_actor` and unresolved builtin `spawn` | Exactly two `TransferOut` facts remain for each | TEST_BLOCKED |
| Lookalike owners | Lower aliases named `pty_spawn` from unrelated or suffix-looking owners | Exactly two `TransferOut` facts remain for each | TEST_BLOCKED |

These scenarios exercise actual HIR call lowering and serialized MIR assertions.
They preserve the existing actor/thread classification; they do not establish
that the wider spelling-based classifier or domain mapping is complete.

The real source fixture at
`test/fixtures/compiler_entrypoint/pty_spawn_transfer_owner/main.spl` imports and
calls `std.sys.pty.spawn as pty_spawn`. Each rebuilt Windows Phase2/Phase3
producer must compile it, and each output must return zero and print
`pty spawn owner PASS`. Invalid arguments exercise wrapper validation without
creating a child. Live ConPTY behavior requires the separate smux system tests.

Execution is blocked by the unavailable qualified test runner and new producer.
The retained diagnostic Stage2 executable predates the patch; it cannot verify
this repair. Once a rebuilt producer is qualified, run the executable spec and
fixture, preserve positive assertion counts and runtime results, then regenerate
this manual through the repository docgen workflow. Do not convert pending rows
to PASS from source inspection, fixture compilation alone, or this authored file.
