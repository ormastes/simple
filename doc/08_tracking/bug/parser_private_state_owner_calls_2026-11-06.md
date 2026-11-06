# Parser state accesses must remain inside their owner modules

Status: source repair prepared; native verification pending.

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
