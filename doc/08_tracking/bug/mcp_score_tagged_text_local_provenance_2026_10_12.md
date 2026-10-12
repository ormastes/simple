# MCP score text-local inference corrupts native formatting

Status: OPEN. This is distinct from unresolved f64.to_int dispatch.

The exact PR3175 formatter compiled with the provisional pure-Simple a45 producer (object5776 bytes) and strictly linked against its generated core-C47/backfill935 pair (ELF2203480 bytes). Native assertions failed. A second source-bound diagnostic preserved the formatter and printed actual results: 0.0 => `0.<decimal pointer>`, 1.25 => `1.<decimal pointer>`, and all six samples had pointer digits as their fraction.

Object disassembly proves the f64 cast emits cvttsd2si and integer arithmetic. Initial str(frac) emits rt_raw_i64_to_string. The final concatenation incorrectly invokes rt_raw_i64_to_string on frac_s's stored text pointer before rt_strcat_tagged. Thus object/link success does not establish score behavior.

Third/final targeted qualification adds a tagged explicit text annotation to frac_s. It is a workaround proposal, not a compiler repair. No fourth score cycle is permitted. Original failure, instrumented output, objects, binaries, commands and receipts are retained in cycle1 and cycle2. The complete MCP binary remains unqualified.

Final result: cycle3 explicit-text candidate compiled6544 bytes and linked2203952 bytes, but native assertion still failed. The annotation did not repair the emitted behavior. Three-cycle STOP; no accepted score workaround or compiler repair.

## Reproduction

Copy the adjacent `.spl.repro` attachment to a tracked `.spl` file in an isolated diagnostic project. Compile with the recorded a45 pure-Simple producer, then strictly link with the recorded canonical __simple_main startup and core-C47/backfill935 pair. Expected assertions cover six formatted numeric values. Actual native exit is1. No scalar contract, whole MCP or compiler repair PASS is claimed.

The renderer intentionally returns a tagged text handle carried as nominal i64. The renderer marks its result as tagged text, but the final local is nevertheless rendered as a raw integer. The precise owner that loses or misinterprets the marker is still under investigation. Replacing the representation with an opaque raw text pointer would be an incorrect repair. Explicit text annotation also failed in the final permitted cycle.
