# MIR final-function scratch survives module scope

Status: source and standalone fixture statically reviewed; grouped regression integration authored, native assertions and RSS benefit UNRUN.

The final413-module native diagnostic completed HIR and monomorphization, then exceeded8GiB during MIR: exit88, peak8,392,880KiB, quiescenttrue. Last progress:64/413,50succeeded,14failed. This does not prove scratch tables account for the whole peak. Evidence remains under `.simple/storage/build/phase3-mcdc-initializer-export-20261015/mcdc-token-stack-native-probe/`.

`lower_module_transient_scoped` promotes its completed MIR and lowerer fields before closing the existing scope. The final function leaves28 LocalId-indexed scratch carriers in the shared lowerer; the next function unconditionally replaces these containers. Promoting those carriers first makes their abandoned no-GC allocations permanent. Invoke existing `reset_function_local_tracking` after module lowering, while scope is active and before promotion. Required output, declaration/default/nominal/layout facts, diagnostics and counters retain their separate owner roots. Reset replaces containers; it does not free or mutate aliased output nodes. Refused scope begin preserves the existing unscoped fallback.

`test/02_integration/compiler/mir_function_scratch_scope_probe.spl` exports the actual scoped/unscoped production-lowerer check. The existing `mcdc_required_token_probe.spl` calls it after its existing alias/ordering checks, so one heavy native closure exercises both. The check requires a real parameter index before reset, empty scratch afterward, expected I64 signature and nil return, exact function MIR serialization parity, reuse, and earlier output survival across a second scope. Package both sibling files together so the relative import remains intact. The helper has no entry main; the existing probe remains the sole entry. Both PASS lines must be observed after native execution.

No physical-RSS or full compiler object/link PASS is claimed. AST eviction and later HIR eviction remain reference-only on the no-GC lane. Full HIR and required MIR outputs still accumulate. Separate semantic failures and the supported runtime's measured reclamation must be qualified before closing the memory target.

## Changed-producer attempt

The combined 414-module native probe on `bd86d7ac` again exceeded the 8 GiB cap: exit 88, peak 8395612 KiB, quiescent with no escaped process. Its last coarse progress marker was MIR 64/414, 50 succeeded and 14 failed; later diagnostic records cover 48 owner modules, so 14 is not a terminal failure total. No executable was produced and neither native PASS line ran. Physical RSS improvement is not established.

Evidence: `.simple/storage/build/phase3-mir-owner-scratch-cycle2-20261016/heavy-terminal-assessment/`. The original controller result remains `RUNNING` because the supervisor killed it; the separate assessment preserves that result and binds the authoritative RSS receipt. Diagnostics include a separately reproduced optional nominal enum-payload failure. Further whole-closure retries need a concrete new cause and a bounded plan; no unchanged memory retry is implied.
