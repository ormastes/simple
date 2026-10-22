<!-- codex-research -->
# Native macOS Simple Container: local code map

The selected route runs macOS programs on macOS and SimpleOS programs on
SimpleOS. No guest OS or VM is involved in either route.

`src/lib/common/contracts/container/runtime_v1.spl` owns copied identity,
operation, state, and transition values. `host_capability_v1.spl` now admits
`macos/macos/native-sandbox` and `simpleos/simpleos/native-container`; it
rejects virtual-machine requests and cross-OS native execution. The matching
SDN codec preserves the isolation class.

`src/os/services/container/container_runtime.spl` and
`runtime_provider_v1.spl` already own SimpleOS managed launch and scheduler
exit reconciliation. The managed launcher currently imports a removed loader
entry; bug 355 blocks a source-matched SimpleOS launch claim.

`src/lib/nogc_sync_mut/io/process_ops.spl` contains pinned executable and
process-observation APIs, but its V3 capability requires Linux pidfd/start
identity and its V4 capability reports `available=0`, `ENOTSUP` outside Linux
(`src/runtime/runtime_process_owned.c`). The pure-Simple observation owner is
also gated unavailable by unfinished ABI, deadline, and tree-cleanup proofs.
The macOS process-observer fixture uses snapshots and cannot establish exact
descendant containment. No usable Mac process lease or App Sandbox authority
exists behind these shared facades today.

A Mac provider therefore needs a native Mac observation owner as well as a
signed App Sandbox launch route. It must verify sandbox state and child policy
before advertising `launch_capable=true`. No such provider or live
native-sandbox fixture exists.

The earlier QEMU/HVF preflight and guest dispatcher are an unselected VM
experiment. Their evidence cannot qualify native macOS Simple Container.
