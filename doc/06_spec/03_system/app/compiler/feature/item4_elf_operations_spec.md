# Static ELF operational composition

Source: `test/03_system/app/compiler/feature/item4_elf_operations_spec.spl`.
Requirements: ITEM4-REQ-001, ITEM4-REQ-004, ITEM4-REQ-007.
Status: **UNRUN**; authored manual, not generated execution evidence.

| Scenario | Independent observation |
|---|---|
| Canonical owner | Explicit sealed operations, legacy wrapper and structural alias produce identical image bytes |
| Relocation dispatch | Real checked relocation with symbol plus one emits `35 12 80` instead of `34 12 7f` |
| Provider permutation | Reordered relocation callback changes bytes; receipt binds each facet to its actual provider slot and engine consumer |
| Layout dispatch | Entry and PT_LOAD addresses move by 4096; real `__ehdr_start` relocation matches selected header load base |
| Writer dispatch | Actual writer output retains selected OSABI byte 9 and valid fixture data |
| Configured wrappers | Retained root survives GC; strip removes `.symtab` and `.strtab` |
| Missing operation | Each omitted required provider prevents sealing |
| Duplicate provider | Repeated provider descriptor prevents sealing |
| Offer/callback mismatch | Missing callback or extra unoffered callback prevents sealing |
| Selected error | Each of three operation errors propagates through full linking without an image |
| Malformed result | Short relocation data, missing layout vector, truncated writer output and a serialized PT_LOAD address contradicting the selected plan reject |

The original narrow-relocation fixture bytes are not recreated in test
callbacks: fixtures are read from disk, parsed, resolved, laid out, relocated,
and written by production code. Custom callbacks delegate actual operations;
only negative cases deliberately inject errors or malformed operation results.

The additional header fixture is built from `operations_header_x64.s` in
`test/fixtures/linker/elf`, using:

```sh
clang --target=x86_64-unknown-linux-gnu -c operations_header_x64.s -o operations_header_x64.o
llvm-readelf -r operations_header_x64.o
```

LLVM inspection confirmed R_X86_64_16 at offset 0, R_X86_64_8 at offset 2,
and R_X86_64_64 against `__ehdr_start` at offset 3. This establishes fixture
provenance only. No Simple runtime or generated executable was run.

After runtime admission:

```text
<runtime> test test/03_system/app/compiler/feature/item4_elf_operations_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts
<runtime> spipe-docgen test/03_system/app/compiler/feature/item4_elf_operations_spec.spl --output doc/06_spec --no-index
```

The eleven scenarios use static caller-trusted callbacks. They do not certify sandboxing,
bounded memory, dynamic loading, hosted execution, or complete item 4 readiness.

Pending execution follows [the item4 native execution gate](item4_linker_execution_gate.md).
This command is an unexecuted recipe, not proof that the current CLI or generated
entry is admitted. Account for all 11 declared scenarios and their actual
assertion behavior; zero reported examples or missing scenario results cannot pass.
