# Reverse-reference facts escape module allocation scopes

Status: reviewed design, source candidate; native and performance acceptance pending.

Base: `2aaadbf544a84e1e032c24090d523cb0b417cbb8`.
This is a prerequisite for safe existing streaming lowering, not proof that the
full-CLI 7 GB limit is met. Default streaming selection is unchanged.

The phase collector is begun before lowering. Streaming HIR registers parser
source aliases inside its transient scope, declaration lowering publishes
annotation facts, and MIR publishes initializer families/dependencies. Those
calls used to append scoped values into process-wide facts/families/alias maps.
The existing HIR/MIR escape inventories did not retain these owners. A later
module or incremental snapshot could therefore read freed records. Promoting
the entire growing phase graph per module would add repeated traversal work.

The candidate captures only module additions in a managed batch. A token binds
capture/seal/publication/abort to one owner and phase. Existing phase records and
the pending batch participate in deduplication and reads, preserving insertion
order. Alias lookup uses a separate scratch dictionary, avoiding a new quadratic
scan of the module's complete alias list. Only the complete batch Option and its
flat retained arrays are promoted; scratch lookup is severed before scope end.
Publication happens outside the allocation scope and performs no second fact
deduplication or whole-phase promotion. Existing fact deduplication still scans
the prior facts; this patch makes no claim to optimize that existing algorithm.

Retained HIR, streaming HIR, and owned MIR boundaries carry exact tokens. Resource
or ownership failure aborts before close. Recoverable parse/semantic errors keep
already-observed facts via successful seal/end/publication. MIR's pre-existing
allocation-scope refusal fallback remains unchanged and acquires no new token.
No direct collector producers were found in ordinary parsing or surface creation.

`test/fixtures/reverse_reference_ownership/main.spl` provides a standalone real
collector comparison with first-cold large capture and later varied small modules.
The paired SSpec rejects absent receipts and checks semantic parity, lifetime,
strict live-object reduction, scaling, elapsed time and externally observed RSS.
All native results remain UNRUN. Failed promotion is rejected and requires abort;
native fault-injection coverage for promotion failure remains an additional gate.

Integration must preserve the generation-aware parser/error ownership changes
from PR2208 and after-pause diagnostic capture from PR2213 in overlapping driver
helpers. This source slice alone does not qualify full-inventory, coverage, shared
cache transitions, or default streaming. Full feature parity and capped native
memory/performance measurements are still required.
