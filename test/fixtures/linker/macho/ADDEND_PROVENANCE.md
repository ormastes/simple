# Hosted ARM64 ADDEND fixtures

Author-created assembly, compiled from repository root with installed
`C:/Program Files/LLVM/bin/clang.exe`, version23.1.2, LLVM revision
`85ac560262434c9ccfc0c183ec22d4138ed647fb`:

```text
clang.exe -target arm64-apple-macos11 -c test/fixtures/linker/macho/addend_local_a64.s -o test/fixtures/linker/macho/addend_local_a64.o
clang.exe -target arm64-apple-macos11 -c test/fixtures/linker/macho/addend_provider_a64.s -o test/fixtures/linker/macho/addend_provider_a64.o
clang.exe -target arm64-apple-macos11 -c test/fixtures/linker/macho/addend_import_a64.s -o test/fixtures/linker/macho/addend_import_a64.o
clang.exe -target arm64-apple-macos11 -c test/fixtures/linker/macho/addend_subtractor_a64.s -o test/fixtures/linker/macho/addend_subtractor_a64.o
llvm-readobj.exe --relocations test/fixtures/linker/macho/addend_local_a64.o
llvm-readobj.exe --relocations test/fixtures/linker/macho/addend_import_a64.o
```

Both final relocation dumps succeed. Local object has twelve records: six
type10 prefixes followed by PAGEOFF12/PAGE21/PAGEOFF12/PAGE21/BRANCH26/BRANCH26
at offsets20/16/12/8/4/0. Prefix payloads16/16/4096/4096/4/4 use flags0xa4.
Imported object has prefix+BRANCH26 at0 referencing `_helper`.

SHA256:

| Object | Digest |
|---|---|
| addend_local_a64.o | f5ed59768c60d40ba571dec4066de21e6147d5559b68fef08884e4db4a6ddbf2 |
| addend_provider_a64.o | 3ea26bd9aa67de41c7623e03b4c63cc8f21017875a60f3078639528ece8737a3 |
| addend_import_a64.o | a1a5fe1dab46781c03ee9b4ee31583e57589b9af374be8c47c2d6c30f003dddd |
| addend_subtractor_a64.o | e0597743701fdae8c85bc0df2165ffbc627da1ca11ca9a5726b67447c560a609 |

The subtractor fixture's LLVM relocation dump independently confirms
SUBTRACTOR then UNSIGNED at dataoffset0. Raw words are0x1e000003/0x0e000004,
referring to `_branch_target` and `_data_target`; no ADDEND record is involved.

Negative addends in tests are **documented wire mutations**, not claimed direct
assembler output. During fixture development, clang23 negative literals emitted
prefix info0xfffffff8/0xfffffffc, spilling signed bits into flags/type instead
of0xa4fffff8/0xa4fffffc. LLVM23 objdump/readobj and LLVM21 readobj aborted with
`Malformed MachO file`; that intermediate object was replaced, and no retained
hash is claimed. The final positive object avoids that external-tool defect;
tests verify all prefix/follower words before replacing only signed24 payloads.
No external linker or Darwin execution proof is claimed.

Provider text starts with a NOP then `_branch_target`; caller text is28bytes,
so the hosted target is textfile0x4020. With no imports, no stub reservation is
needed: data is0x8000, containing77 then `_data_target` value88 at0x8008.
With the imported fixture, one import reserves the0x8000 stub page; zero-addend
BL reaches that stub and nonzero imported addends are deliberately unsupported.
