# NUL literal constructor copies tagged string metadata as content

Status: OPEN. Real native failure and causal input boundary confirmed; narrow
source repair and prevention regressions authored, candidate execution unqualified.

## Actual failure

Producer d3563806c3babfe69358380aa752a0b90b65f7119a7b83cb441a97a969ca9791
(`/mnt/c/Temp/simple-p2-bounded-read-runtime-relink-20261012/simple`) compiled a
32-control-byte literal and mixed `before\0after` literal. The resulting text
began `RTS\x01` instead of the authored bytes. Quote/backslash, UTF8 and empty
cases without NUL passed. This corruption is independent of JSON escaping.

The emitted `__simple_main` calls `rt_string_new_literal(raw, 32)` and then
`rt_string_new(tagged_result, 32)`. Actual GDB observation at the latter call:
input lowbits=1, header kind bytes `31 52 54 53`, reserved=1, stored length32,
and original data exactly0..31. Before entering the escape helper, the second
registered object's data already starts `52 54 53 01` and metadata; length32
alone still passes. This identifies a caller ABI mismatch, not a runtime join
or escape-helper defect.

Evidence: `/mnt/c/Temp/simple-nul-literal-abi-20261012/input-boundary.log` and
`input-boundary.gdb`. Original actual object and executable remain under
`/mnt/c/Temp/simple-mir-json-control-escape-20261012`.

A separate byte-only native probe avoids JSON, slicing and escape helper imports.
Its private Git fixture compiled with the same admitted producer in8.731seconds,
peak process-tree69616KiB, object6664bytes; strict paired link exit0; execution
exit1, stdout `FAIL NUL literal local`. It checks the authored four-byte `A\0é`
using length and byte_at. Receipt/source identity and exact commands are retained
as `baseline-*-receipt.json` and `baseline-command.json`. Resource limits were
120seconds and2GiB; neither fired. Runtime archive47a386651d02839e9ec1cf86c41728105e827ce32d6f5fbef32497582f9d7993
and compiler backfill935f72674326bbf1042d4c4ce8bfdb1fccf4796242e8a418db65d7744a3ac723
were used, without stubs or replacement compiler fallback.

## Cause and repair boundary

Both exact producer source b58baa89e4d65a40768fceaf8221fdbdbe58da24 and candidate
base d4dd079c531af40d6cd8938a3b92f9496e03f4b9 contain the same NUL-only extra
constructor in `_MirLoweringExpr/expr_dispatch.spl::lower_expr` StringLit arm.
It previously emitted Opaque(str) then passed that local to raw rt_string_new.
The backend already boxes Opaque(str), producing the double-boxing error.

The candidate scans for NUL before emitting the constant and selects Ptr(U8)
only for that constructor's byte input. Its declared first parameter uses the
same pointer type. Explicit authored length, constructor result/tagged marking,
interpolation path and ordinary Opaque(str) literals are preserved. No runtime
unboxing, option handling, symbol renaming or global ABI change is introduced.
Only the selected type is constructed; ordinary literals gain no extra raw-type
object. No post-change latency, memory or leak-freedom claim is made.

Current backend source contracts reviewed:

- LLVM `_MirToLlvm/core_codegen.spl::translate_const` boxes only Opaque(str)
  through emit_boxed_text_literal_into; Ptr constants keep raw rodata addresses.
- Cranelift `cranelift_codegen_adapter.spl::cl_translate_const_value` returns the
  raw data address for Ptr and otherwise boxes ordinary text constants.
- The direct frontend C generator and interpreter do not use this MIR literal
  construction branch. They are not claimed tested by this repair.

Linux/SOSIX LLVM baseline executed. Candidate LLVM/Cranelift and Windows, macOS,
BSD, SimpleOS,32-bit/interpreter/C-generator compatibility remain unexecuted.

## Prevention and qualification remaining

`test/01_unit/compiler/50.mir/nul_literal_raw_constructor_operand_spec.spl`
uses the actual parser,HirLowering and MirLowering. It asserts raw NUL constant
bytes/type, constructor parameter type, copied operand identity and exact length;
empty/ASCII/UTF8 non-NUL literals remain Opaque(str) without the extra constructor.
These are authored real assertions, not a string search or a mirrored lowering.

`test/02_integration/compiler/nul_literal_raw_constructor_native_probe.spl`
checks local, argument, return, leading/trailing NUL, empty, ASCII and UTF8 bytes.
Only its first failing check ran on the old producer; later cases and all candidate
cases remain unexecuted. Existing llvm_typed_text_literal_box_spec tests backend
MIR inputs directly and cannot catch this preceding frontend insertion.

Two bounded diagnostic cycles were used: existing-object GDB, then independent
native byte probe. No speculative third compiler closure build, no shadow-source
admission and no fourth whole-runner retry. The old binary cannot validate a
source overlay of its compiler. Actual candidate producer qualification and real
frontend regression execution are required before marking fixed or landing.
Separate existing counted-text slicing through strlen and JSON control escaping
remain outside this literal repair.

## Next qualification inputs (2026-10-12)

Latest duplicate check: release_phase3 `3e6da6a19a3a3ad0f11e2d6419dcd1dcdc06d5ba`
still has the defective branch; both reviewed backend owners are unchanged from
this candidate base. No new admitted producer is available. Linux CI38169694975
(source27b236a51c20dbb43765740c05d8d94d45f36a7e) and Windows CI38169498820
(source67698a03ae2d3fdbe82a575a91504956b9d8d660) were still live when inspected
by the coordinating agent; neither is candidate qualification evidence.

At the next causally required build restart, include this reviewed source patch
in the frozen compiler source and preserve its manifest. First qualify the new
producer with real Hello compile/link/run. Then compile the standalone byte probe
with that producer and paired runtime, execute all eight cases, and run the real
frontend-MIR spec. Inspect output/disassembly to ensure one counted constructor
receives raw rodata rather than a prior boxed handle. Repeat on the other backend
or label it unexecuted. Source-only overlays with d356, stale cached providers,
renamed ABI symbols or fabricated cache admissions cannot qualify this repair.
No extra build was started merely to wait for those existing CI jobs.


## Historical and current qualification

The d356 probe above is historical and still fails. The later frozen old-DAE 9fd literal-owner facet passed real Hello and 28 scoped text/byte checks; see the [merged DAE evidence appendix](nul_literal_double_box_constructor_2026_10_12_dae_evidence.md) and its exact receipt hashes. Those are distinct fixtures and lineage, not execution of this latest source composition. The current source, frontend/MIR specification, original eight-case native probe, generation and mandatory compiler/library/MCP/LSP core gates remain unexecuted/unqualified. This corrective source PR stays DRAFT; no production acceptance or memory-safety PASS is claimed.

## Local composition qualification

Transferred from upstream PR #3311 onto local release_phase3 `15616ab39c5bb206e6976dd520e3d09b257fa915`.
Production repairs and regression files in this composed candidate are
AUTHORED_UNEXECUTED. Historical upstream receipts above are not execution
evidence for this source composition or the current ARM/RISC-V compiler.
Status remains OPEN; full Phase3 and required verification remain pending.
