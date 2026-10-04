# Streamed ELF common symbols

Source: `test/03_system/app/compiler/feature/item4_stream_common_spec.spl`.
Requirements: ITEM4-REQ-003, ITEM4-REQ-004, ITEM4-REQ-009.
Status: **UNRUN**. Authored manual; no admitted Simple runtime or RED/GREEN evidence.

| Scenario | Independent oracle |
|---|---|
| Maximum size/alignment | Different declarations supply size 80 and alignment 64; relocated references share one zero-filled RW allocation |
| Undefined archive common | Both engines extract a real COMMON-only provider and satisfy the same semantic oracle |
| Strong precedence | Regular strong initializer wins over common in both input orders |
| Weak precedence | Common zero storage wins over regular weak initializer in both input orders |
| Archive selection | Strong member selected; larger common and weak members remain absent, including a mixed archive traversed from undefined references |
| Other-symbol archive demand | Member selected for `trigger` contributes its size-4096/alignment-256 common declaration |
| Malformed declarations | Zero/non-power-of-two alignment and local COMMON reject even when a strong definition could override them |
| Logical budgets/cancellation | Output, scratch, scan-work and cancellation failures retain an existing destination sentinel |

The eight scenarios inspect a unique marker and three real relocated pointers, then translate
addresses through PT_LOAD headers. Stream output has no required symbol table.
Zero storage is checked in file bytes or ELF-defined zero-fill. Nonoverlap and
alignment are checked independently. The initial streamed RW extent must be
112 bytes: one 80-byte allocation, 16-byte alignment gap, one 16-byte allocation.
Eight- and 64-byte emission windows must produce identical stream images.
Fast/stream comparisons use semantic checks rather than identical layouts.
Quota and cancellation checks also enter common layout with real retained
inputs already open, exercise its scan guard, and close the original owner.

Fixture sources are `test/fixtures/linker/elf/stream_common_*.s`. Each object was
assembled with Ubuntu clang using `--target=x86_64-unknown-linux-gnu -c`.
Archives use `llvm-ar rcs`; single-member archives contain their matching object.
The mixed archive order is `stream_common_archive.o`, `stream_common_unused.o`,
`stream_common_weak.o`, `stream_common_strong.o`. LLVM symbol inspection confirmed
the independent size/alignment declarations. These are fixture-construction
results, not Simple verification. GNU ld archive-selection research is recorded
in the lane design/research documents.

After runtime admission:

```text
<runtime> test test/03_system/app/compiler/feature/item4_stream_common_spec.spl --native
<runtime> spipe-docgen test/03_system/app/compiler/feature/item4_stream_common_spec.spl --output doc/06_spec --no-index
```

Secure task-specific directories isolate outputs. Completed paths remove owned
files and require the scratch parent to become removable. Cleanup failures
remain assertion failures. Resident test oracles do not measure production RSS.
Whole-job memory enforcement, hosted execution, other architectures and overall
item 4 readiness remain separate open gates.
