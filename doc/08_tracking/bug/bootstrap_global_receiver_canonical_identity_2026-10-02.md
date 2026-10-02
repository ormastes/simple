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
These baseline runs did not execute the fixed compiler.

## Post-fix MIR discriminator

Integrated Linux producer
`8f817f2b6d5430ab6a18f36e8c9e136857783341adfea8741acfe7a5aea552d4`
contains this repair plus the class/LLVM declaration fixes, without the enum
patch. Both fixtures now pass MIR. The local fixture compiles and runs exit 0.
The global fixture reaches LLVM and fails on duplicate `@g_...__gate` definitions,
the independently owned provisional/runtime static-finalization defect
(commit 829d89e72a). Thus the targeted owner-resolution error is eliminated;
global native execution was still blocked at this producer revision.

Evidence: classfix-source-fcb35f85cd/build/global-receiver-proof-20261002 under
the same Linux bootstrap root. Separate private caches and 512 MiB / 60 s
watchdogs were used. The local probe briefly overlapped a separate GDB job's
checkout-wide cold SCV initialization; there were no SCV diagnostics, but these
results do not claim SCV concurrency validation. Both jobs reached quiescence.

## Native global receiver acceptance

Reviewed Linux producer
`7cc8409e930a6d818016efdbf4df2c1ad575716e6553a3ce41c5a8aba656df29`
from `classfix-source-4e33ca888f` includes this receiver repair and static
finalization `829d89e72a`, together with the reviewed HIR presence repairs.
The previously blocked global fixture compiled exit 0 and executed exit 0,
with the expected empty stdout. Its SHA256 is
`dca33ffa90e090d9ba1565ed50d975f0a92971e78bbea0a4ce69ecb9da1f277a`.
The already-passing local control was not rerun.

The producer-bound private cache/output is
`build/global-receiver-proof-7cc-20261002` in that checkout. Retained copies are
under `D:/dev/global-receiver-proof-7cc-20261002`: identity hashes, compile/run
logs, result and watchdog receipt. The enforced 512 MiB / 60-second process-tree
guard recorded peak RSS 254,884 KiB, exit 0 and `quiescent=1`. It reports
`hard_memory_limit=0`; enforcement is the sampled process-tree RSS watchdog.
The checkout-wide cold-SCV writer was released before the next owner's probe.

This is native acceptance of the global receiver fixture with the required
static-finalization integration. The producer excludes the enum-pattern and
imported-global-binding candidates, so those are not validated by this run.
Full compiler/lib/MCP smoke and cross-host qualification remain pending.
