# Interpreter coverage unary-not leaves

Requirement: REQ-INTERPRETER-MCDC-UNARY-NOT-LEAVES.
Bug: BUG-INTERPRETER-COVERAGE-UNARY-NOT-LEAVES-20261011.
Executable: test/01_unit/compiler_core/interpreter/coverage_unary_not_probe_spec.spl.

Activate the real runtime collector with `SIMPLE_COVERAGE=1`. The spec uses
actual AST arenas, source spans, evaluator initialization, and the canonical
no-GC synchronous coverage facade. It does not mock evaluation or probe storage.

| Criterion | Actual evidence |
| --- | --- |
| Negation preserves operand condition identity/truth | Leaf101 is recorded true; wrapper201 is absent; expression returns false. |
| Negated conjunction preserves short-circuiting | False leaf301 is recorded; unbound right operand401 is not evaluated; conjunction501 and negation601 are absent; expression returns true. |
| Operand errors propagate | Missing operand returns-1; leaf701 and wrapper801 have no invented condition receipt. |

Stage1 Windows bootstrap diagnostic only. Base95c12f073ffefa99ac774264beeedd68a47e7676,
producer SHA25615102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb,
host windows/AMD64, target x86_64-pc-windows-msvc. Original owner2/2 FAIL;
repaired owner2/2 PASS. The raw extern fixture was replaced by the canonical
facade, and that genuinely changed dependency input passed2/2. A focused new
error criterion passed1/1 without repeating the first two greens. Incremental
three-criterion PASS is not a final full-suite rerun or runtime admission.

No skips/drops or compiler rebuilds. Evidence receipt, terminal logs, SDN probe
rows, source-only SFFI audit, and environment guard logs live under
build/phase1-coverage-not-20261011. Parent source review found noP0/P1 in the
unary recursion and error propagation. The regression adds zero raw rt externs.

Status: diagnostic PASS; native/pure-Simple admission PENDING. Compiler/lib/MCP
checks, MCP stdio integration, core runtime smoke, and MCP native smoke require
an admitted release runtime. Both Windows release runtime paths are absent.
The production PR stays draft. The four historical bounded/legacy/vector
fragment criteria remain unchanged and OPEN; no historical backlog closure is
claimed by this narrower behavioral repair.
