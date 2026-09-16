# Pure-Simple HIR Module GPU Metadata Transport Loss

## Status

Closed. The loss was caused by a stale Rust-seed interpreter impl-method index,
not HIR or MIR aggregate transport.

## Symptom

A caller reads `hir.gpu_function_targets["copy"] == "vulkan"`, but
`MirLowering.lower_module` sees empty metadata in the `HirModule`, its
`SymbolTable`, and extracted `HirFunction`. Explicit dictionary and parallel-array
arguments are also empty when added around this large compiler aggregate.

## Historical Evidence

Command:

```sh
SIMPLE_COMPILER_TRACE=1 sh scripts/check/check-vulkan-source-storage-buffer-abi.shs
```

Observed for all three source cases:

```text
[mir-gpu-explicit] name=copy targets=0 target_hit=false orders=0 selected_kernel=false selected_target=
```

The source spec asserts the caller-side module and symbol metadata before the
call. The verifier then failed 0/3 because `[u32]` parameters remained MIR Arrays.

The focused
`test/01_unit/compiler/interpreter/dict_field_argument_transport_spec.spl`
passes direct and aggregate-field dictionaries through free functions, one- and
multi-parameter `me` methods with defaults, local aliases, and parallel arrays.
It also passes a roughly 90-field mixed aggregate through free and `me` calls,
including head/tail dictionary and array reads plus post-construction assignment
from local dictionary/array values. Free
functions receiving the real `HirModule`, `SymbolTable`, and extracted
`HirFunction` preserve their GPU metadata. The defect is therefore specific to
`MirLowering.lower_module` rather than general aggregate or receiver transport.

Assigning early parallel metadata arrays from array locals yields zero-length
arrays on entry, including with copy-modify-reassign. Literal arrays containing a
direct map lookup or a verified scalar local contain nil. Constant text literals
survive as `1/1/1` in all three cases and remove the original Vulkan pointer
diagnostic. A split-module probe also reads a literal-assigned field correctly.
The focused constant transport was retained during diagnosis; temporary layout
probes were removed.

With constant `"vulkan"` and `""` metadata, lowering advanced to three independent
defects: source `-> ()` is emitted as a value-returning Vulkan entry, invalid i32
buffer elements are not rejected, and immutable-buffer assignment reports
`variable span not found` while building its diagnostic.

The public `lower_function` wrapper reads early kernel/target selection from
`func_attr`, falling back to the appended scalar fields. Direct positional,
named-target, and backend-order wrapper cases pass, but complete-module ordered
backend transport remained 8/9. Removing the literal source-test transport also
regressed all three Vulkan source ABI cases because parameters lowered as Arrays
before late GPU decoration. A qualified global scalar registry and free-function
module extractors were both tried and removed after producing no improvement.
The literal-only `MirLowering` arrays were retained as a focused test harness,
then removed after the dispatcher repair passed without them.

The bounded follow-up also ruled out three smaller fixes. Explicitly rebinding
every `module.functions.values()` element to `HirFunction` left the source ABI
at 0/3 and complete-module metadata at 8/9. Replacing aggregate target-selection
field reads with scalar normalization helpers left the source ABI at 0/3.
Finally, consulting the authoritative `SymbolTable` metadata inside the shared
`lower_function` wrapper also left the source ABI at 0/3 and was removed. In all
three source cases, Vulkan still receives MIR Array type tag `1984125491` rather
than Ptr/U32; both negative cases produce no MIR diagnostic. The scalar helper
experiment also exposed a VHDL backend-order semantic mismatch and is not proof
of repaired transport.

A subsequent interpreter review found the root defect in the Rust
seed method dispatcher: its `(class, method)` cache trusted an index from an old
`impl_methods` slice even when a later registry had a different order. The shared
lookup now validates the cached index against the current method name and rebuilds
only stale entries. Its focused reordered-registry regression passes 1/1. This is
a plausible owner because `MirLowering` spans many `impl` blocks. After an
incremental seed rebuild, the source Vulkan ABI suite passed 3/3, emitted assembly
passed `spirv-as` and `spirv-val` for Vulkan 1.3, and complete-module GPU metadata
passed 9/9. Removing the three temporary `MirLowering` transport arrays preserved
the same 3/3 and SPIR-V validation result.

## Next Check

No transport workaround remains. Keep the reordered-registry unit test and the
source ABI plus SPIR-V verifier as regressions. A future normal release/bootstrap
will deploy the seed fix; no full bootstrap was needed for this diagnosis.

An incremental `bin/simple check` of `_MirLowering/module_lowering.spl` also
failed to complete within the standing 60-second CPU monitor limit and exited
255. This is retained as a tooling-performance blocker; no bootstrap or retry
with a raised timeout was attempted.
