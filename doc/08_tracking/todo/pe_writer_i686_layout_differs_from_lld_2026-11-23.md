# TODO: Pure Simple PE writer section layout differs from lld (i686 hello)

**Filed:** 2026-11-23 | **Area:** compiler/linker (pure-Simple COFF/PE) | **Type:** output parity
**Status:** OPEN

## Gap
The i686 hello linked by the Pure Simple linker (`coff_link_driver.spl`)
runs and prints the same as the lld link. `llvm-readobj` still shows these
differences from lld:

- It emits `.gfids`, `.00cfg`, `.CRT`, `.ctors`, `.dtors` and `.text$im` as
  separate output sections. lld merges `.text$*`/grouped sections and folds
  these into `.rdata`/`.data`/`.text`.
- `.bss` appears twice.
- No import from `api-ms-win-core-synch-l1-2-0.dll`; lld's image has one.
- `.debug_*` and `.buildid` are dropped: file 405 KB vs 575 KB, SizeOfImage
  11,624,448 vs 11,661,312.

Same in both: machine 0x14c, PE32, image base 0x400000, subsystem,
header/DLL characteristics, the imported symbol set otherwise, `.eh_fram`.

## Fix
Apply COFF grouped-section merging (`$` suffix ordering, then the standard
`.CRT`/`.tls`/`.gfids`/`.00cfg` -> `.rdata`/`.data` merges lld does), merge
duplicate `.bss` contributions into one output section, and find which
object or archive member contributes the `api-ms-win-core-synch` import.
Keeping or dropping debug sections should be an explicit option.

## Evidence
Images, `llvm-readobj` dumps and logs from the Pure Simple linker lane:
`C:\Users\user\AppData\Local\Temp\claude\07e8ec21a8a8dcf3\fc765f87-77cb-46a6-a5ae-ba02303d093e\scratchpad\h2`
(session scratchpad, not durable; re-run the i686 hello link to reproduce).
