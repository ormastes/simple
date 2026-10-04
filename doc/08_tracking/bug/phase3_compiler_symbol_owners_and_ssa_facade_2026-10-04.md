# Phase3 compiler symbol owners and unresolved SSA facade

Status: three caller import repairs prepared; native retry pending. The generic
SSA facade-resolution defect remains unresolved and has a retained regression.

## Exact observed input

The diagnostic packet is
`runtime/windows-restart-20261004/diagnostic-phase3-restart-80/cranelift/`.
Its `source-git-head.txt` pins `6f79558dfa6efab8724518f3d57c0ddf3f6d3415`;
`phase2-producer.sha256` pins the Cranelift Phase2 executable to
`eaf207cc7ae52aeee7145714d989ed32a6c0e4e49aa5f6f47eb3ac9de153cf8e`.
`hir-diagnostics-decoded.json` reports three `fields_push` diagnostics against
`outline_decls.spl`, one `local_count_increment` against `var_reassign_ssa.spl`,
and four export/name diagnostics for the two SSA transform functions against
`_MirToLlvm/core_codegen.spl`. These are eight diagnostic rows, not eight tests.
The packet is explicitly provisional and does not prove dynamic providers.

The repair worktree is based on release
`b0f0cf98787037095280e0c9f6bc2911829b0e11`, confirmed against the remote before
editing. The separate `expr_mark_colon_block` failure already has its explicit
import on this release; this patch does not duplicate or change that repair.

## Two missing imports

`outline_decls` invokes `fields_push` for class, actor and struct fields but
only imports `methods_push` from the declaring `outline_members` module.
`var_reassign_ssa` invokes `local_count_increment` when identifying locals with
multiple definitions but omits it from the declaring `var_reassign_analysis`
import. Both repairs add the existing owner symbol; algorithms are unchanged.

## SSA facade failure remains tracked

Both `ssa_var_transform_blocks` and `ssa_alloca_transform_blocks` are already
explicitly re-exported by `60.mir_opt/__init__.spl` in the failing source and
the repair base. Adding duplicate exports would not address this failure.
`module_import_resolution` emits `has no exported item` from the frozen
surface/re-export lookup before registering the callable body; therefore the
missing `local_count_increment` is not proven to explain the facade miss.
The backend now imports the two implementation helpers from their canonical
declaring module, `compiler.mir_opt.mir_opt.var_reassign_ssa`. This repairs
that caller's ownership edge without claiming the public facade resolver is
fixed. No facade API is removed or renamed.

`mir_opt_facade_ssa_owner_spec.spl` deliberately retains public-facade imports
and executes nonempty MIR renaming and stack-slot transformations. It must
eventually pass with the rebuilt native compiler; it is not skipped, marked
expected-failure or rewritten to a direct import. Existing
`llvm_array_value_copy_single_ssa_def_spec.spl` also uses the facade and checks
LLVM output. Native execution of these cases is pending the root-owned cached
rebuild, not a claimed PASS.

## Verification plan

The existing TreeSitter class test now checks two field names and their order,
in addition to the class count. Existing var-reassignment, runtime-array SSA
and LLVM array-copy specs exercise the repaired owner. The new facade case
keeps the unresolved route visible. No build/test launch was made while system
commit headroom was low. Source snapshots, selected diagnostics and static
checks are retained in the external `phase3-compiler-symbol-owners` packet.
