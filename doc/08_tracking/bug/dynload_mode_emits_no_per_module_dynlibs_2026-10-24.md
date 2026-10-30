# `--mode dynload` emits no per-module dynlibs; no import library (.dll.a)

Status: open (feature gap). Found 2026-10-24 while adding per-dynlib link
receipts (held PR #4356).

## What exists today
- `native-build --mode dynload` is the default mode
  (`src/app/io/_CliCompile/compile_targets.spl` ~:881). It produces the native
  artifact plus an ordinary SMF (`output_format_both`, ~:1459) and warns
  `W-NATIVE-BUILD-DYNLOAD-ASPECT-PACK-NOT-PRODUCED` (~:262). It does **not**
  partition the build into per-module (or per-package) shared libraries.
- The only shared-library link is `--emit-shared`
  (`src/compiler/80.driver/driver_aot_native_output.spl` `emit_shared_requested`
  -> `link_to_shared`), which links ONE library per build from all objects.
- `_link_shared_windows` (`src/compiler/70.backend/linker/_LinkerWrapper/shared_linking.spl`)
  produces the `.dll` only; no `.dll.a` / `.lib` import library is emitted.

## Consequence
"A changed object relinks only its own dynlib" cannot hold yet: there is one
dynlib per build, so any changed object relinks all of it, and importers have
no import library to keep stable.

## Plan (per-dynlib)
1. Partition: group modules into dynlibs (per package / per `simple.sdn`
   target, entry executable separate). Each dynlib = its own object set.
2. Per-dynlib link receipt (implemented in #4356,
   `native_shared_link_with_receipt_v1`): key over that dynlib's objects in
   link order + every NativeLinkConfig field + runtime-path digests; receipt
   records the export digest (`llvm-nm --defined-only --extern-only`).
   A changed object relinks only its dynlib; no change = no relink.
3. Windows replacement: link under the same base name in a private temp dir,
   rename the loaded `.dll` aside, rename the new one in, delete the old when
   possible (a loaded DLL can be renamed, not deleted).
4. Import library: emit `<name>.dll.a` (llvm-mingw: `-Wl,--out-implib`) and
   regenerate it ONLY when the export digest changed; importers relink only
   then.
5. Loader: the entry executable resolves dynlibs by name next to it; dynload
   SMF / aspect packs keep their current role.

## Evidence
`native_link_receipt_v1_spec` 6/6 on the seed (receipt export digest
round-trip, rename swap with failure recovery). Steps 1, 4, 5 are not
implemented.
