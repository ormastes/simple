# Class owner identity scenarios

Source: test/unit/compiler/hir/class_owner_identity_spec.spl.
This companion is hand-authored pending SPipe execution/doc generation; it is
not a passing test receipt.

| Scenario | Action and expected observation | Requirement |
| --- | --- | --- |
| Imported class aliases | Resolve LeftCell/RightCell; IDs differ and bare Cell does not leak. | REQ-001 |
| Windows owner spelling | Define through an absolute src path and dotted module; IDs agree. | REQ-001 |
| Nested type relocation | Collide provider/consumer numeric IDs; nested Array/Optional/Named selects the provider class and preserves the consumer binding. | REQ-003, REQ-004 |
| Default helper and capture | Relocate a helper call to its provider name; reject a colliding capture only when its default is consumed. An explicit field argument succeeds. | REQ-004 |
| Two layouts | Register right then left; canonical layouts and default helper names remain distinct and no foreign bare Cell appears. | REQ-002, REQ-003 |
| ABI names | Keep extern/export/@global names; qualify provider main and retain actual entry main. | REQ-005 |
| Ownerless bootstrap functions | Use the active owner to resolve helper/global names and recognize function values. | REQ-005 |

The isolated native fixture additionally exercises same-named nested Leaf
classes, constructor overrides, static/instance methods, impl/Self, a reexport
facade, helper main, local/imported function values, and runtime array push. Its expected process exit is zero.
Native execution and codegen inspection remain pending (REQ-006, REQ-007).
