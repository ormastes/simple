# C4 typed SOURCE specialization: initial scalar subset

Status: source implementation for review; all executable checks UNRUN.
This does not qualify an actual SOURCE invocation or the full selected scope.

`compiler.mir.source_region_specialize_module_v1` owns the initial transform.
Its inputs are an actual MIR module, resolved entry SymbolId, resolved context
type, resolved private facade SymbolIds, the existing SymbolTable allocator,
and canonical Result construction operands supplied by the actual MirLowering
owner. Function names resolve a direct MIR operand only to a unique existing
module function; names never allocate or authenticate specialized identities.

The finite visited closure reuses C3's direct-call resolver and region-effect
manifest. Unsupported mutable effects remain explicit obligations. The typed
instruction planner must classify them before specialization. Unknown calls,
indirect targets, foreign execution, raw memory provenance and unsupported
allocation/container operations reject the selected entry.

The transform plans all original instructions before allocating specialized
symbols through `define_with_binding(..., bind_lexical: false)`. Each specialized
signature receives one trailing SourceRegionContextV1 argument, its actual
LocalKind.Arg local, and an outer Result. Recursive/internal edges forward that
same local. Ordinary functions and callers remain present with their original
signatures. Allocation/initialization/store sequences consume typed facade
Results before any subsequent initialization/publication operation.

The initial subset requires original i64 returns and scalar parameters. Every
specialized return is Result<i64,E>. A successful original return uses the
canonical constructor operand/runtime enum identity supplied by the real owner.
An operation or internal-call Err returns its original Result unchanged; no
error payload is discarded or reinterpreted. A malformed discriminator calls
the exact resolved Incomplete factory. Cleanup belongs to the actual retained
consumer entry wrapper, which is not supplied by this module transform.

Metadata is assigned only after rewriting: exact hidden local, ABI 1, and a
digest binding the original closure, typed transformed bodies, descriptors,
facade declarations and Result construction identity. Module metadata retains
the resolved context declaration identity and matching digest. Ordinary empty
metadata does not authorize SOURCE execution. Nonempty metadata is included in
canonical MIR serialization and block replacement preserves it.

Open admission work:

- Actual compilation-request/entry wrapper constructs one context from the
  shared account and retains it through all consumers and cleanup.
- Actual parser/HIR/MIR two-node fixture, alias stamp change, foreign-child
  rejection and native execution; authored unit contracts are not that proof.
- Generic outer Result payloads must use the actual retained per-function
  MirLowering builder and provenance maps. Standalone completed-module state
  cannot reconstruct those maps or reuse the last lowered function's maps.
- Arrays, dictionaries, variants, text, all selected source roots/transport,
  cancellation and backend/provider parity remain independent obligations.

For generic replay, the approved owner path computes the resolved closure once
from provisional MIR, keeps original HIR, then re-lowers each selected function
once on the actual owner and invokes its specialization hook before the next
`reset_function_local_tracking`. Canonical codec temporaries must be allocated
through that actual builder; invented metadata snapshots are not admitted.
