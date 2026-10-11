# Unprojected borrow rejects mutable-local SSA conversion

Status: source repair prepared; native candidate qualification pending.

The module matrix reports duplicate `%l24` and `%l47` definitions in
`pinned_archive_capability.spl`. Both affected functions borrow `adopted_view`.
MIR locals permit repeated assignments; these are valid MIR, but LLVM names
must have one definition per function. `ssa_instructions_supported_for_alloca`
rejected `Ref` and abandoned slotting for the entire function. The existing
LLVM SSA verifier correctly rejected the resulting duplicate definitions.

`llvm_ref_impl` represents an unprojected borrow as an identity on its source
value (including an object/reference handle). The repair admits that case and
updates alloca read rewriting, destination renaming, use collection and maximum
local-id calculation together. A slotted borrow source is loaded before the
borrow; the borrow must not point at the slot itself. A slotted borrow result
is renamed and stored. Borrow kind and place metadata are preserved. Projected
places remain rejected; their address semantics are not inferred here.

Reproducer: `test/fixtures/compiler/ssa_borrow_merge/main.spl`. Producer
`/home/yoon/dev/simple-bootstrap-mir-object-20261011/build/native_probe/combined-fixes/simple`,
SHA-256 `67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`,
base source `78eb2dbc4c0b0128ab0d63fbf1b6b40007f9c9cd`.
Before repair, native object compilation exits 134 after `unsupported
instruction` and `llvm-emitter-ssa-violation:...borrow_with_merge:%l7`.
Log: `build/native_probe/ssa-borrow/before.log` in the isolated
`simple-astra-ssa-local-20261011` worktree. The real fixture has one source
module and needs no CUDA/archive runtime facilities.

Structural spec: `test/01_unit/compiler/mir_opt/ssa_alloca_borrow_spec.spl`
checks both read/write slot ownership, high source IDs, and projected-place
rejection. Runtime execution of that spec is pending a qualified full runner.
The existing duplicate-SSA verifier is unchanged. No object or runtime PASS
is inferred from source review.
