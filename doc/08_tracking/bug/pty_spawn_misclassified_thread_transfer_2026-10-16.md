# PTY spawn alias misclassified as a thread transfer

ID: `BUG-PTY-SPAWN-THREAD-TRANSFER-2026-10-16`.
Requirement: `REQ-SMUX-WINDOWS-PTY-SPAWN-OWNER`.

Status: fixed in source only; executable verification pending a rebuilt
Pure-Simple producer. This is not a Phase2/Phase3 admission receipt.

## Retained failure

The Windows smux diagnostic build used the unadmitted p3sync Stage2 executable
with SHA-256
`06ccfabd9aaed34fdf7bda5e4b170ee28678a0549fa9bb5dc3b995eb522e855c`.
Its diagnostic remains in
`build/smux-windows/phase2-p3sync-06ccfabd/simple-aot-diagnostic-bd476e2b8a1e45800b9a09804547566d/message`.
The diagnostic file's retained last-write timestamp is
`2026-10-16T00:28:08.1264231Z`. It contains the failure twice:

> compile error: LLVM runtime transfer-envelope lowering is not implemented [module=os.apps.smux.api function=os.apps.smux.api.smux_pane_spawn_pty at=:0:0]

The failure happened after 46 other native objects were emitted, according to
the parent build lane. No admitted receipts or Stage3 producer existed for
this attempt. This repair does not rewrite its evidence or relabel that
producer, and no Rust seed was used for verification.

## Cause and owner

`src/os/apps/smux/api.spl` imports `std.sys.pty.spawn as pty_spawn`, then calls
`pty_spawn(handle, command_line)`. The public PTY declaration validates those
arguments and invokes `rt_pty_spawn`; its arguments identify a process launch,
not a task or actor payload ownership transfer.

HIR import registration correctly records the defining module and restores the
physical declaration name `spawn` while keeping `pty_spawn` as the scope lookup
alias (`module_import_registration.spl`). MIR's ordinary direct-call lowering
then classified every direct callable named `spawn` or `spawn_actor` as a
Thread transfer boundary, independent of its resolved declaration owner.
Consequently it emitted `TransferOut` for each PTY launcher argument.

LLVM's explicit rejection is correct for a real unsupported transfer. MIR's
instruction contract requires validating and lowering a transfer envelope;
changing `TransferOut` to a plain copy would silently discard ownership
semantics. Cranelift likewise has no matching implementation: its generic
unsupported-instruction arm rejects these operations. The pure-Simple transfer
contracts/codec are not a native backend runtime ABI implementing the missing
ownership handoff.

## Scoped repair and regressions

`MirLowering.call_has_thread_transfer_boundary` retains the old spawn checks
except for the exact resolved PTY declaration owner. Existing owner
canonicalization folds `std.sys.pty`, `lib.sys.pty`, and the physical
`src/lib/sys/pty.spl` leaf to `lib.sys.pty`. Alias text and suffix matches are
not authority. Ordinary call argument lowering still runs; LLVM fail-closed
transfer diagnostics remain unchanged.

`test/01_unit/compiler/mir/pty_spawn_transfer_boundary_spec.spl` contains five
scenarios exercising the actual HIR call-lowering path: aliased PTY import,
canonical/physical/Windows owners, actor spawn, actor/builtin legacy spellings,
and lookalike non-PTY owners. Positive transfer scenarios require exactly two
`TransferOut` instructions. These assertions preserve existing actor/thread
classification rather than claiming its domain mapping is universally correct.

`test/fixtures/compiler_entrypoint/pty_spawn_transfer_owner/main.spl` is a real
source import/call regression. Compile it with the rebuilt Windows Phase2 and
then Phase3 producers and run each result; it must return zero and print the
checked-in expected stdout. Its invalid arguments exercise the PTY public
wrapper without creating a child. This fixture proves alias call compilation
and argument validation; the smux ConPTY scenarios must still prove live
terminal behavior.

No compiler tests or native fixtures were executed in this repair lane: the
general runner remains blocked, and the available diagnostic executable
predates this patch. A new qualified producer is required before the parent
lane retries smux. Source `git diff --check` passed for the compiler edit.

## Pending fixture command

The following is a template for the build owner, not an executed receipt.
`$rebuiltProducer` must identify a rebuilt Pure-Simple compiler containing this
repair. Run once with the qualified Phase2 producer and distinct Phase2 output
and cache paths, then once with the qualified Phase3 producer and distinct
Phase3 paths. Record executable SHA-256, frozen source revision, linked runtime,
exit status, and stdout for each. Do not point it at the retained old producer.

```powershell
& $rebuiltProducer native-build --source src/lib --source test/fixtures/compiler_entrypoint/pty_spawn_transfer_owner --entry-closure --entry test/fixtures/compiler_entrypoint/pty_spawn_transfer_owner/main.spl --backend=llvm --cache-dir $fixtureCache --output $fixtureExe
& $fixtureExe
```

Expected compile exit status: `0`. Expected executable exit status: `0`.
Expected stdout (checked in beside the fixture): `pty spawn owner PASS` followed
by a newline. The unit SSpec and its mirrored manual are respectively
`test/01_unit/compiler/mir/pty_spawn_transfer_boundary_spec.spl` and
`doc/06_spec/01_unit/compiler/mir/pty_spawn_transfer_boundary_spec.md`.
Their current execution/docgen status is `TEST_BLOCKED`.

## Remaining wider classifier risk

Other ordinary functions named `spawn`/`spawn_actor` can still be falsely
classified, while qualified spellings and task/actor domains need a coherent
semantic boundary identity registry. The semantic transfer checker also has
independent spelling-based classification. This narrow PTY owner correction
does not fix those wider issues or implement native transfer envelopes.
