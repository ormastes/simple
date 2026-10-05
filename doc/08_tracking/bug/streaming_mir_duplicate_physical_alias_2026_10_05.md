# Streaming MIR emits duplicate objects for logical source aliases

Status: source candidate; native qualification pending.

Both native backends failed `src/app/sfm_samples/vcs/main.spl` under producer
3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb,
target source b0b36be5e4ee78bded9de2e3f89e6a6bbc669d54, streaming surfaces on,
HIR sharding off and one native worker. The preserved task packets are
`executable-batch20-buildrunner-fix1/{cranelift,llvm}-023-vcs` under the
Windows restart evidence root.

HIR completed three modules and captured three typed receipts. Native output
successfully compiled four modules, with four object paths and four accepted
capsule identities, zero objectless modules, then correctly refused publication
with `cold-object-inventory-incomplete`. The extra native object is
`std.sfm.manifest`, alongside the canonical
`lib.nogc_sync_mut.sfm.manifest` for the same physical source. The other two
modules are VCS main and vcs_layer. This is not a failed linker or lost object.

Streaming parsing deliberately retains alias SourceFile rows because frozen
module surfaces and parallel owner arrays use original source indices. It
deduplicates HIR through the physical surface registry. MIR formerly iterated
all retained rows and emitted one module for each spelling. Nonstreaming parsing
already selects the first row per physical source with
`_driver_unique_physical_sources`.

The candidate reuses that existing helper to form a local MIR work plan for
the cross-module prescan and direct lowering loop. Work counters/progress use
that plan. It preserves original ctx.sources, scalar owner arrays, module
surface indices, aliases used for name resolution, and all full-inventory and
cold native-object completeness guards. There is no receipt-count exemption or
alias spelling heuristic at publication. The first physical source remains the
same representative chosen by streaming surface construction.

## Required native qualification

- Recompile the original VCS entry on both backends, source/producer and cache
  identities pinned. Require three HIR receipts and three native owners, no
  duplicate std.sfm.manifest object, actual successful link. Do not execute the
  original VCS application: its commit operation is outside this regression.
- Compile and run streaming_mir_physical_alias/main.spl, requiring four check
  lines, exact completion and exit0. Repeat with streaming surfaces off to
  prove the same behavior. Empty/no-import and one-import Hello are neighbors;
  distinct physical sources must continue to produce distinct native objects.
- Retain the complete original source-index arrays and validate module-surface
  lookups after planning. Exercise reordered aliases, duplicate logical names
  from different physical sources (must still fail the existing collision
  gate), and full-inventory mismatches (must remain rejected).
- Compare old and fixed MIR/native work counts, elapsed time and peak RSS using
  the same wrapper. Removing duplicate work is source-proven; elapsed or memory
  improvement is not claimed before execution.

The fixture and original failed-entry retries have not run on a compiler that
contains this change. Source review and diff checks do not qualify the fix.
