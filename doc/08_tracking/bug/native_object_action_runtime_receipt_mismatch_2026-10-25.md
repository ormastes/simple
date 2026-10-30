# Native object action incorrectly requires executable runtime receipts

Status: OPEN; source candidate, production qualification pending.

The CLI success funnel classified `--emit-object`/`--emit-entry-object` as
`artifact_kind=object`, then required the executable runtime-provider manifest
and dead-strip linker receipt. The driver returns its copied/relocatable
aggregate object before the runtime linker publishes those receipts. The
manual macro diagnostic retained an aggregate and successfully linked/ran it,
but honestly recorded `coordinator_raw_status=1`, `mir_shard_contract=FAIL` and
`normal_compiler_build=NOT_QUALIFIED` in
`build/verify/macro-scalar-sharded-manual-system-link-20261025-01/result.env`.
Manual linking does not repair that parent failure.

The candidate adds a distinct Darwin relocatable-object action-input identity.
It binds the actual codegen provider, current tool/producer ABI, sources,
dependency and imported closure, target/CPU/deployment/SDK, optimization and
object format. It requires actual matching-CPU MH_OBJECT bytes. Only the object
contract requires the executable runtime-artifact and linker-tool fields to be
empty; no runtime manifest, linker receipt or sentinel runtime hash is invented.
Binary/shared runtime admission stays mandatory. Archive behavior is unchanged.
The object action-input receipt does not certify copy-versus-aggregate tool
execution; empty executable-link fields do not mean no relocatable linker ran.
The driver's existing admitted object-input rechecks, linker resolution and
nonzero-status handling remain unchanged.

Astra statically reviewed the four production/test files on base
`1d2bc6658144aa9a2a676c095780685e3486a54e` (diff SHA256
`1fc23f0622fadae44767e36f6f5e2b5dacba4148f6ac5b1041faf2014574df16`).
One retained-gen13 interpreter unit transaction ran under a 3 GiB process-tree
cap and 120-second bound: **18 executed, 13 passed, 5 failed, 0 skipped/dropped**.
All six added object contract/kind examples passed. The five failures occur in
unchanged external-executable identity examples, with the retained seed reporting
no compiler-owned dynamic-SFFI ABI contract for `malloc`; no baseline execution
or fix for that separate failure is claimed. The complete suite is not green.
Peak observed RSS was 424816 KiB and final quiescence was 1. Changed source,
header parser, seed and all retained-generation runtime authority hashes stayed
identical before/after. Evidence:
`build/verify/native-object-action-identity-unit-20261025-03/` in the release
review worktree. Owners 01/02 refused before compiler execution due missing
sparse-checkout guard files; they provide no test evidence.

The production Native `--emit-object` CLI integration is authored but
**UNEXECUTED**. No P2, Rust, runtime or native compiler build ran. A
source-containing producer must pass the original object-producing coordinator
transaction before its raw failure can be called fixed or the normal compiler
build/MIR-shard contract can be qualified.
