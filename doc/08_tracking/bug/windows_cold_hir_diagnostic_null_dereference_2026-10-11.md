# Windows cold HIR diagnostic null dereference

Status: source repair verified by native bootstrap diagnostics; pure compiler qualification pending.

The Windows Stage 2 compiler crashed while compiling
`src/app/bootstrap_builder/native_group_provisional_main.spl`. The producer
SHA-256 was `62b9104ec2ad4f8a1bb75d5923cc78b55b761cc9c3e8f84a8010a8d4d7f5c37c`,
from source revision `0c7bb72f83663c4407e694af1388109be25d7ac3`.

A bounded CDB diagnostic captured a natural first-chance access violation in
worker 21820 at 2026-10-11 18:04:40 KST, before its 900-second deadline.
At executable RVA `0xae8ee4`, `mov r15,[rax+8]` read address 8 with RAX zero.
The earlier failed build's peak RSS was below its enforced memory limit;
this is an invalid lookup/dereference, not evidence of a memory-limit kill.

Matching the executable's unwind function extent against its original COFF
object, masking relocation bytes, uniquely identified
`CompilerDriver.capture_cold_hir_typed_receipts_v1+0xc34` in
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`.
The preceding instructions call `rt_dict_len`, construct integer zero, call
`rt_index_get`, mask the returned value, then dereference its path field.

The source diagnostic used `hir_modules[0].path` after checking only dictionary
length. `hir_modules` is a `Dict<text, HirModule>`; nonempty does not establish
an integer-zero key. The missing lookup produced nil. This secondary crash
masked the original `cold-hir-module-source-mismatch` validation failure.

The repair obtains the first source's module name only when that owner is
nonempty, checks that the dictionary contains the name, and then reads its
path. Missing diagnostic data retains an empty path. The original receipt
error and failing return remain unchanged; this repair does not admit an
invalid source/HIR binding or establish resolution of the underlying mismatch.

Local evidence is retained under
`C:/dev/simple-phase4-evidence/crash-authority-20261011-attempt2/`, including
`first-av-debugger.log`, `first-av.dmp`, `symbol-mapping.jsonl`, and
`source-owner.md`. The minidump SHA-256 is
`55c6449b6c53a5ce2b2ffe41aa9be71a0911e92fa54ce963f02a4c209d6d47d4`.
The diagnostic debugger and its matching compiler processes were confirmed
absent after capture. Debugger exit zero is not compiler success or admission.

## Verification

The exact production error block was extracted into a typed minimal fixture.
The original block compiled with the diagnostic seed's LLVM backend, then
crashed with exit 139. The repaired block passed an exact 20-line output oracle
on native LLVM and Cranelift: empty dictionary, missing name, empty name list,
present name, and empty source list. All five preserve the failing return;
the present-name case must print the actual matching HIR path.

The old pure Stage 2 compiled and executed the repair without crashing but
failed that semantic oracle, printing numeric text handles and omitting the
present HIR path. This is tracked separately in
`windows_stage2_typed_text_array_diagnostic_mismatch_2026-10-11.md` and is not
counted as a passing pure compiler regression. Diagnostic seed results do not
grant compiler admission.

`scripts/check/check-cold-hir-path-diagnostic.shs` packages the extraction and
strict oracle with explicit producer/runtime/backend inputs and fresh private
outputs. Packaging received syntax/static checks; the execution evidence above
comes from the preceding hash-bound extracted fixtures, not a rerun of the
packaged adapter. Full bootstrap, whole-suite and product-build qualification
remain separate requirements. The frozen newer-source bootstrap has not yet
incorporated this repair.
