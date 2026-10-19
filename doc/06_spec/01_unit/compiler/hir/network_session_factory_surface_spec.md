# Network owning-factory surface scenarios

Authored manual; all five actual parser/HIR API scenarios are **UNRUN**.

1. Parse the production TCP class and require exactly six public methods, no raw adoption helper, and private fields.
2. Parse the production UDP class and require exactly five public methods, no raw adoption helper, and private fields.
3. Build actual module surfaces and require a cross-module private aggregate constructor diagnostic.
4. Build actual module surfaces and require a private transport field diagnostic.
5. Confirm a public owning factory has no HIR diagnostics in the same setup.

These cases call the frontend and HIR APIs. They are not source-substring tests, runtime privacy proof, or affine-lifetime qualification.
