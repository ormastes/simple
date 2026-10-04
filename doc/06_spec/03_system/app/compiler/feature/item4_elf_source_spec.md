# ELF selected file-source acceptance

Source: `test/03_system/app/compiler/feature/item4_elf_source_spec.spl`.
Requirements: ITEM4-REQ-001, ITEM4-REQ-002, ITEM4-REQ-007.
Status: **UNRUN**. Authored manual; no admitted Simple execution evidence.

| Scenario | Observation |
|---|---|
| One selected owner | Real alternate source makes ELF `base` equal to 7; the same owner's real writer sets OSABI 9 |
| Canonical source | Default and explicit file-aware owner produce identical ELF bytes with `base` equal to 2 |
| Selected read error | Named injected callback error leaves destination sentinel intact |
| Missing source facet | Existing three-facet owner rejects both empty and absent-file inputs before reading |
| Invalid real inputs | Absent, empty, and non-ELF files leave destination sentinel intact |
| Output alias | Alias error takes precedence over the selected error callback; input remains unchanged |
| Hosted snapshot reuse | Selected source reads a real archive then poisons its task-owned path; hosted image still contains `base` equal to 7 |

The hosted scenario requires Linux x86_64, real CRT files, libc and the dynamic
loader. Missing prerequisites fail assertions or return a named production
error; they are not counted as skipped passes. It builds a hosted ELF image
through the production internal adapter, but does not execute that image.

Fixture commands from `test/fixtures/linker/elf`, using Ubuntu LLVM:

```sh
clang --target=x86_64-unknown-linux-gnu -c source_provider_x64.s -o source_provider_x64.o
clang --target=x86_64-unknown-linux-gnu -c source_hosted_main_x64.s -o source_hosted_main_x64.o
llvm-ar rcs source_provider_x64.a source_provider_x64.o
llvm-readelf -s -x .data source_provider_x64.o
llvm-readelf -r source_hosted_main_x64.o
```

Executed fixture inspection confirmed the provider's eight-byte `base=7`
initializer and the hosted main's PLT32 reference to `add_val`. These external
tool results do not establish Simple RED/GREEN.

After runtime admission:

```text
<runtime> test test/03_system/app/compiler/feature/item4_elf_source_spec.spl --native
<runtime> spipe-docgen test/03_system/app/compiler/feature/item4_elf_source_spec.spl --output doc/06_spec --no-index
```

The portable source returns resident byte snapshots. Coverage establishes
selected callback consumption and reuse between classification and linking,
not change-during-read detection, immutable identity, retained handles, or a
bounded working set. Test-owned files are removed after completed scenarios;
there is no retained-handle cleanup claim. Full item 4 host/runtime and memory
gates remain open.
