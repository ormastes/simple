# Global receiver loses canonical class identity

Windows lifecycle closure reports unresolved AtomicI64 `load` and
`compare_exchange`. A Linux no-import discriminator reproduces the same split:
local `GateCell` reaches LLVM emission, while a global of the same declared type
fails MIR on both methods. Neither atomic FFI nor imports are required.

`lower_type(Named)` emits `MirTypeKind.Struct(canonical_id)`, where canonical IDs
start at 1,000,000,000 and do not belong to the HIR symbol table.
`try_lower_global_read` previously queried `symbols.get_symbol_raw(canonical_id)`
when registering receiver provenance. The lookup misses, and unresolved method
recovery does not enter its owner path without that provenance. Local factory
results receive their provenance through separate return metadata.

Repair: use the existing `mir_struct_symbol_name` helper at the existing global
registration site. It resolves canonical IDs and preserves module-qualified class
identity, so two same-named imported classes cannot alias here. No extra global
registration, runtime dispatch shortcut, or diagnostic bypass is introduced.

Evidence producer: Linux SHA256
`184d1be492926713d19bfb95ba2705cb31a2fb6affe8ebea9e1874185d6ef921`.
Evidence directory:
`/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/classfix-source-623b7943f1/build/atomic-receiver-discriminator-20261002`.
`local.log` reaches LLVM then fails on an unrelated `rt_alloc(nil)` declaration;
`global.log` fails MIR with unresolved `load` / `compare_exchange`. Each probe
used its own cache and a 512 MiB / 60 second process-tree watchdog. Both exit 1.
This establishes the pre-fix discriminator, not native execution success.

Focused spec checks the real global-read hook with two canonical class owners.
Positive native fixtures are `nominal_receiver_local_native.spl` and
`nominal_receiver_global_native.spl` under `test/fixtures/compiler/`.
Post-fix compiler rebuild, test execution and native execution remain pending.
