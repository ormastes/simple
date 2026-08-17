# Pure-Simple dynamic frontend-to-HIR Tuple crash

**Status:** open
**Area:** dynamic frontend/HIR execution

## Reproduction

Cache-free pure-Simple execution of a dynamically parsed function fails before
`HirLowering.lower_function`:

```sh
bin/simple test test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl \
    --mode=interpreter --no-session-daemon --sequential --no-db --no-cache \
    --assert-ran --fail-fast
```

Observed error:

```text
semantic: undefined field: unknown property or method 'kind' on Tuple
```

The failure remains when the function explicitly declares `-> ()`, so it is
not caused by untyped-return inference. The focused
`vulkan_gpu_attr_hir_spec.spl` now passes 4/4 for Vulkan, CUDA, and Metal source
metadata, including an explicit `-> ()` regression.

2026-07-31 boundary probes proved every parameter lowers and enters the HIR
parameter array. The flat parser was converting empty tuple type `()` to
`TYPE_ANY`; it now registers the empty tuple through the existing tuple-type
registry. The bridge consequently reconstructs `TypeKind.Tuple([])`, and the
frontend owner helper uses a discriminant-gated typed pattern to extract its
elements. A second boundary showed scalar built-ins must also bypass traversal
of their malformed empty generic-argument payload on this dynamic path. The
focused explicit-Unit/scalar HIR regression passes 4/4 with both repairs; the
full source ABI verifier has not run after the combined fix because its
three-cycle cap was already exhausted.

## Scope

The HIR Tuple/flat-optional blockers are cleared. Backend probes showed the
first argument local and signature share the same non-pointer discriminant;
the test's broad `MirTypeKind.Ptr` match was a false positive. The upstream
`lower_vulkan_kernel_param_type` also used broad unqualified `Array | Slice |
Int` patterns and returned the ordinary MIR array type. It now dispatches on
qualified HIR discriminants, extracts array/slice elements in isolated guarded
matches, and emits the Vulkan pointer/U32 ABI. Backend argument/interface scans
are likewise discriminant-gated. A subsequent probe showed `func_attr` becomes
nil after HIR function collection even though it is populated immediately after
HIR lowering. `HirFunction.func_attr` is now concrete `FunctionAttr`, using
`FunctionAttr.default()` for absence like the existing desugared aggregate
metadata fields. Because the nested concrete struct still reset during
`HirModule` transport, `HirFunction` now also carries primitive
`is_gpu_kernel`, `gpu_target`, and `gpu_backend_order` fields. HIR constructors
and copy passes preserve them, and MIR uses them for ABI selection/final
metadata while retaining `FunctionAttr` for non-GPU attributes. Because passing
the full `HirFunction` still truncates trailing fields, module lowering extracts
those three primitives before the call and passes them separately to
`lower_function_with_gpu_metadata`. Focused HIR passes 4/4 and MIR GPU metadata
passes 8/8. A full parser-to-HIR-to-MIR metadata regression added by an
independent sidecar passes 9/9.

The first fresh cache-free source ABI verifier turn ran three times after the
metadata repair and failed 0/3 at the argument ABI guard. A second fresh turn
added discriminant assertions for both signature parameters and argument
locals; they pass immediately before codegen. An expanded backend diagnostic
then proved argument 0 local 0 and its signature parameter retain the same
pointer tag (`1984125491`) inside Vulkan, while pointer predicates still return
false. Passing the owner and then the scalar tag through helper functions did
not change that result. The remaining fix is therefore to compare the already
computed local tag with pointer/U32 tags directly in `compile_compute_shader`,
without a helper boundary. Do not rerun the unchanged verifier or use the Rust
seed as acceptance evidence.

The next fresh turn removed helper boundaries and compared tags directly, but
three verifier cycles still failed 0/3. Canonical runtime hashing proves
`Ptr = 422722806`, `Ref = 59990695`, and `U32 = 1163175990`; the source-lowered
signature and argument local both carry `1984125491`, which is canonical
`Array`. Both positional and named `MirTypeKind.Ptr` construction attempts in
the lowering path still produced Array. The source regression now pins the
canonical hashes so it cannot validate itself with a second mis-lowered Ptr
constructor. Repair pure-Simple payload enum construction before resuming the
unchanged Vulkan verifier.

That constructor diagnosis was too strong. Three fresh controlled attempts
(primitive target normalization, inlining Vulkan parameter conversion, and
recovering kernel metadata from `FunctionAttr`) each left the exact same
canonical Array tag and 0/3 result; all three changes were removed. The next
turn must observe `gpu_kernel_target`, branch activation, and the constructed
tag immediately before `params.push`. Until then the evidence proves only that
ordinary Array reaches Vulkan, not where the intended Ptr conversion is lost.

The direct trace then proved the branch state: `primitive_kernel=false`, raw
and normalized targets empty, `attr_kernel=false`, and `vulkan_branch=false`
for every parameter. A module-owned name-keyed GPU target/order map now captures
metadata before functions enter the lossy dictionary and is preserved by
resolve/effect passes. The existing metadata suite remains 9/9, but it does not
assert those maps, and the third source cycle still failed 0/3 with Array. Next
assert map population immediately after HIR and after resolve before changing
MIR again.

Independent sidecars also added fail-closed signature/argument-local bijection
validation and rejected immutable-StorageBuffer to mutable-GEP escalation. The
new mutability regression passes; its containing intensive spec reports 38
passes and two pre-existing failures. The bijection worker's targeted run timed
out in the existing daemon and remains unverified.

## Re-triage 2026-08-17 (m9a_tests lane)

**Verdict: the named spec is not a shell-out reproducer — scoping note.**

`test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl`
contains no subprocess call: `grep -n "process_run\|bin/release\|bin/simple"`
over it returns **zero hits**. Per the session brief, a spec body runs
INTERPRETED, so this spec cannot exercise the "cache-free pure-Simple execution
of a dynamic frontend-to-HIR path" the doc describes — that path is only
reachable from a separate `bin/simple` process. Whoever picks this up must add
a subprocess shell-out (pattern:
`test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl`) or the
reproduction will be vacuous.

Note also that the deployed `bin/simple` here is the **Rust bootstrap seed**,
so a "pure-Simple execution" claim cannot be settled on this host at all until
a self-hosted binary is available.

**Not reproduced from this lane.**
