# effect_inference_spec

*Source: `simple/std_lib/test/features/concurrency/effect_inference_spec.spl`*

---

Effect Inference - Feature #46

Overview:
    Compiler automatically infers async/sync effect from function body. Suspension
    operators (~=, if~, while~) indicate async, pure computation indicates sync.
    Mutual recursion handled via fixed-point iteration. Eliminates need for
    explicit async/sync annotations in most cases.

Syntax:
    fn double(x: i64) -> i64:           # Inferred as sync
        return x * 2

    fn fetch_data() -> Data:            # Inferred as async (uses ~=)
        val d ~= http.get(url)
        return d

Implementation:
    - Analyzes function body for suspension operators
    - Suspension operators (~=, if~, while~) imply async
    - Pure computation implies sync
    - Propagates effects through call graph
    - Handles mutual recursion via fixed-point iteration
    - Type-driven await inference based on target type
    - Formal verification in Lean 4

Notes:
    - Formal properties verified in Lean 4: determinism, suspension implies async,
      sync safety, effect propagation
    - Eliminates need for async keyword in most cases
    - Effect propagates through function calls
    - Planned feature - not yet implemented
