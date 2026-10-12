# OPEN: colon slice omitted end disagrees with native legacy provider

Status: OPEN. Severity: P1. Source fix not landed or executed by a source-containing producer.

Core colon parser emits -1 for omitted end and cg_slice_expr forwards it unchanged to spl_str_slice. Core colon interpreter treats negative end as text length. The actual linked runtime_legacy_core.o instead clamps negative end to start, returning empty. The Phase4 process-limit validator consequently accepts an overflow input incorrectly. Original object/probe/GDB evidence: /mnt/c/Temp/simple-process-limit-native-probe-20261012/omitted-end-baseline; producer d3563806c3babfe69358380aa752a0b90b65f7119a7b83cb441a97a969ca9791.

Shared ABI prevents a safe runtime-only rewrite: explicit text.slice(start,end) uses the same spl_str_slice symbol with a different negative-end contract. Preserve that method and runtime behavior. Candidate pure-Simple core codegen normalizes only colon bounds using once-and-order tuple evaluation and a captureless C++ lambda. Its actual production-expression projection linked to real archive47a386/backfill935f passes20 assertions; baseline fails9. This does not qualify execution of the Simple codegen owner or any compiler generation. Source candidate, commands, receipts: /mnt/c/Temp/simple-legacy-slice-contract-20261012/colon-codegen-hygienic.patch and generated-code-hygienic-receipt.json.

Temporary explicit-end source workaround is tracked in PR3231. Old producers retain the defect until a source-containing generation is built and qualified. Embedded-NUL raw-C-string truncation is a separate OPEN defect; this report claims no counted-NUL correctness.

Prevention covers omitted/explicit-negative colon, unchanged negative method, empty/reversed/end bounds/extreme i64, UTF8 byte boundaries, int64 base overload, module initializer/local capture, side-effect order/once and colliding user identifiers. Native Linux projection passed; Windows/macOS/BSD/SimpleOS and full Simple owner execution remain unexecuted.
