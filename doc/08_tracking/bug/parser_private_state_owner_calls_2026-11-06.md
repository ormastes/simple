# Parser state accesses must remain inside their owner modules

Status: source repair compiled successfully with private symbols preserved; broad runtime and SSpec gates pending.

The advice planner baseline attempt 4 compiled 284 modules, reused 37 native
cache entries, and rejected two modules on imported non-public static data.
The canonical guard completed with exit 1, quiescent 1 and peak RSS
10,549,924 KiB. Retained evidence:
`/home/yoon/dev/simple-bootstrap-advice-plan-before-20261106/build/bootstrap-advice-plan-new/before/`.
The failure does not constitute an executed planner assertion.

`extend_decls` directly read pending metadata owned by `enum_module_body`;
`parser_decls_use` directly updated generic constraint dictionaries owned by
`fn_struct_decls`. The backend visibility rejection correctly exposed these
cross-module state accesses. Making the globals public or disabling accessor
checks is not a repair.

`parser_pending_metadata_promote_transient_owner()` now promotes all six
pending metadata arrays inside their owner. Each promotion still wraps the
array in a nested root, promotes that root and frees the temporary wrapper.
Every promotion executes even if a preceding promotion returned false.
`extend_decls` retains promotion of its own arrays and calls the owner function.
`parser_register_file_generic_constraint(name, types, mode)` updates both
file-local dictionaries inside their owner. Reset and snapshot functions are
unchanged, and the declaration facade explicitly exports the functions.

Verification gate: repeat the existing real native planner baseline with these
prerequisites, then the repaired planner, using the pinned Hello-tested producer
and private caches. Planner attempts 1–4 remain consumed; only attempts 5 and 6
remain. No new exploratory build is authorized by this record. Full runtime
checks and source-level parser behavior tests remain pending qualified CLI
availability. No release or Phase 3 admission is claimed.

## Native prerequisite evidence

Planner baseline attempt 5 with this repair built successfully (exit 0,
quiescent 1, peak RSS 14,477,972 KiB). Its executable ran all nine planner
assertions: four expected target-only-plan failures and five passing controls,
exit 4 and quiescent 1. Evidence is retained at
`/home/yoon/dev/simple-bootstrap-advice-plan-before5-20261106/build/bootstrap-advice-plan-new/before5/`.
This proves the formerly failing native boundaries compile and the resulting
executable reaches real planner/readiness assertions. The planner remains
unfixed in that baseline by design.

`owner-symbols.txt` and `owner-symbols-command.txt` retain a one-time inspection
of exact owner objects mapped from `native/build_cache.sdn`. `readelf --wide
--syms` found all six pending arrays and both generic dictionaries as OBJECT
LOCAL, with zero GLOBAL/WEAK or address-accessor symbols matching those state
names. The name-based filter does not exclude arbitrarily renamed accessors;
source review confirms the new functions return no addresses. Preserve this
green evidence for unchanged owner code rather than rerunning the check.

`test/01_unit/compiler/parser_private_state_owners_spec.spl` adds real snapshot
assertions for registration/reset and six-array promotion/value preservation.
Those SSpec scenarios remain unexecuted until the qualified CLI is available;
value preservation does not prove survival after transient scope teardown.
