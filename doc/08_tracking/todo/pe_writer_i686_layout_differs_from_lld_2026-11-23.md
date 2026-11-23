# TODO: Pure Simple PE writer section layout differs from lld (i686 hello)

**Filed:** 2026-11-23 | **Area:** compiler/linker (pure-Simple COFF/PE) | **Type:** output parity
**Status:** PARTIAL (COFF `$` section merging/folding & single `.bss` fixed; debug-section option remains OPEN)

## Gap
The i686 hello linked by the Pure Simple linker (`coff_link_driver.spl`)
runs and prints the same as the lld link. `llvm-readobj` originally showed
these differences from lld:

1. **FIXED:** It emitted `.gfids`, `.00cfg`, `.CRT`, `.ctors`, `.dtors`, and
   `.text$im` as separate output sections instead of folding them into
   `.rdata`/`.text` with `$` ordering.
2. **FIXED:** `.bss` appeared twice when objects had `.bss` input sections and
   common symbols.
3. **INVESTIGATED:** No import from `api-ms-win-core-synch-l1-2-0.dll`; lld's
   image had one.
   - `archive_closure.spl`, `coff_import.spl`, and `pe_import_builder.spl` load
     and emit COFF short imports when archives in `request.archives` provide the
     referenced symbols (including `COFF_WEAK_SEARCH_LIBRARY` weak externals).
   - In this codebase, `api-ms-win-core-synch-l1-2-0.dll` (`WaitOnAddress`,
     `WakeByAddressSingle`, `WakeByAddressAll`) comes from MinGW's
     `-lsynchronization` (`libsynchronization.a` / `synchronization.lib`), passed
     on external `clang`/`lld` paths (`shared_linking.spl`, `native_all_support.spl`,
     `link_config.rs`), or from `raw-dylib` import descriptors embedded in
     `simple_native_all.lib` (`windows_whole_archive_duplicate_import_descriptors_2026-08-30.md`).
   - By contrast, `scripts/check/check-windows-pe-internal-link.shs` and
     `native_linking.spl` omit `libsynchronization.a`/`synchronization.lib`, and
     `coff_link_driver.spl` calls `coff_link_i386(req)` on explicit `--obj`/`--lib`
     inputs without resolving `/DEFAULTLIB` (`coff_link_i386_default_libraries`)
     and without merging object-embedded `raw-dylib` `.idata$*` sections.
   - Note: the exact Windows `scratchpad/h2` objects/archives from the original
     filing were not present on the macOS verification host, so the specific `h2`
     input archive member was not re-dumped directly.
4. **OPEN (explicit option):** `.debug_*` and CodeView `.debug$*` are dropped by
   `_coff_section_is_image_input` (and `.buildid` is not synthesized); keeping or
   dropping debug sections should be an explicit option.

Same in both: machine 0x14c, PE32, image base 0x400000, subsystem,
header/DLL characteristics, the imported symbol set otherwise, `.eh_fram`.

## Fix Applied (`src/compiler/70.backend/linker/coff/coff_link.spl`)
- Updated `_coff_output_section_name`, `_coff_output_section_rank`, and
  `_coff_subsection_sort_key` to merge `$` subsections lexicographically by
  suffix (empty suffix first) and fold `.text$*` + import thunks into `.text`,
  and `.rdata$*`/`.00cfg*`/`.CRT$*`/`.gfids$*`/`.ctors*`/`.dtors*` into read-only
  `.rdata` (`0x40000040`, clearing `IMAGE_SCN_MEM_WRITE`), while keeping `.pdata`,
  `.xdata`, and `.tls` separate.
- Unified layout in `_coff_layout_sections` so input `.bss`/`.bss$*` sections
  and `CoffCommonLayout` common symbols allocate contiguously into a single
  `.bss` output section (zero raw size), and `_coff_output_section_index` /
  `_coff_output_section_base` match the emitted PE section headers even with
  dropped empty sections or reordered groups.
- Pinned behavior with `test/01_unit/compiler/backend/linker/coff_section_merge_parity_spec.spl`
  and updated `coff_link_spec.spl` and `coff_mingw_crt_spec.spl`.

## Remaining
- Add an explicit option for keeping or stripping DWARF `.debug_*` / `.buildid`
  debug sections.

## Evidence
Images, `llvm-readobj` dumps and logs from the original Windows filing:
`C:\Users\user\AppData\Local\Temp\claude\07e8ec21a8a8dcf3\fc765f87-77cb-46a6-a5ae-ba02303d093e\scratchpad\h2`
(session scratchpad, not durable; re-run the i686 hello link on Windows to
verify live `api-ms-win-core-synch` archive origin and full-binary comparison).
`lld-link /lldmingw` (LLVM 23.1.1) section-folding rules and characteristics
were verified directly against `.rdata`/`.00cfg`/`.CRT`/`.ctors`/`.dtors`/`.text$*`.
