# SimpleOS: the two `default_axes == "static"` faces are rejected by selected-asset validation -- 2026-08-09

## Status 2026-08-17: the read-derived root cause below is FALSIFIED by execution

The hypothesis in this doc -- that `default_axes == "static"` is what makes
selected-asset validation refuse Bungee and UnifrakturCook -- was never
executed. It has now been executed on the host lane
(`bin/simple run`, `load_selected_font_file` on the real staged assets):

```
assets/.../ofl/bungee/Bungee-Regular.ttf            len=118996 valid=true reason=valid
assets/.../ofl/unifrakturcook/UnifrakturCook-Bold.ttf len=42688 valid=true reason=valid
```

Both faces validate CLEANLY, reason=`valid`. The validator handles `"static"`
deliberately: `sfnt_manifest_default_axes_match`
(`src/lib/common/encoding/sfnt.spl:230`) returns `manifest == "static"` when the
font has no `fvar` table, which is exactly these two faces.

So the guest-side `rejected:<n>B` is NOT a `default-axes`/`format` validator
refusal. Per `font_renderer_register_selected_bytes`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:434-452`) the remaining
candidates are `runtime` (validation passed, the `font_runtime_ttf_default_supported`
probe refused) or `identity`. The guest already records which one via
`font_renderer_last_selected_registration_reason()`; that receipt has to be
read off a guest run before this doc names a cause again.

Pinned as `test/01_unit/lib/common/encoding/font_registry_static_axes_validation_spec.spl`
so the falsification cannot silently rot.


## Status: OPEN -- NOT a desktop-text blocker. Root cause below is READ-DERIVED AND UNVERIFIED (nothing was executed for this filing).

## Observed evidence

Surfaced by `acd7196e1d0` ("fix(simpleos): scope desktop font readiness to the
default face, not the whole pinned corpus"), which replaced the whole-catalog
readiness aggregate with per-face receipts. The guest now names the failures
instead of collapsing them to `accepted=0`:

```
[desktop-gui] font register accepted=1 catalog_complete=0 registered=14/16
  unregistered=Bungee=rejected:118996B,UnifrakturCook=rejected:42688B
```

`rejected:<n>B` means (see `_simpleos_desktop_register_candidate_bytes` in
`src/os/desktop/font_bootstrap.spl`) that the bytes were read off the staged
FAT32 image at full length and `font_renderer_register_selected_bytes` refused
them. It is a validation refusal, not a VFS/read failure.

**Bungee and UnifrakturCook are exactly the two entries in the 16-face pinned
catalog whose `default_axes` is `"static"`** --
`src/lib/common/encoding/font_registry.spl:205`:

```
if family == "Bungee" or family == "UnifrakturCook": return "static"
```

The other 14 are variable fonts with `wght=...`/`wdth=...` axis manifests.

This is the opposite of the natural hypothesis. The commit message records a
host probe on the *variable* default face
`assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`
(1,708,408 B): 21-table sfnt with `fvar`/`gvar`/`avar`/`STAT`,
`format.supported=true`, `axes_match(wght=400,wdth=100)=true`,
`instance.supported=true reason=supported-default-glyf`. Variable fonts
validate fine by design; the static pair does not.

## The two affected catalog entries

`src/lib/common/encoding/font_registry.spl:317` and `:321`:

| field | Bungee | UnifrakturCook |
|---|---|---|
| upstream path | `ofl/bungee/Bungee-Regular.ttf` | `ofl/unifrakturcook/UnifrakturCook-Bold.ttf` |
| category | `display` | `blackletter` |
| `byte_len` | 118996 | 42688 |
| `sha256` | `c4f5361c…6bf66e3f` | `ea002fa9…f79a6dcd` |
| `default_axes` | `static` | `static` |
| embedded style / full / PS / version | `Regular` / `Bungee Regular` / `Bungee-Regular` / `Version 2.000` | `Bold` / `UnifrakturCook` / `UnifrakturCook-Bold` / `Version 2011-09-01 ` (trailing space) |

## What was ruled out by reading the on-disk assets

Host-side inspection of the two asset files (read-only: `ls`, `sha256sum`, an
`od` dump of the sfnt offset table, `strings -el` over the name table) shows
every catalog-vs-bytes gate in `_validate_selected_font_asset_with_digest`
(`font_registry.spl:557-609`) should PASS:

- `byte-length`: on-disk sizes are exactly 118996 and 42688 -- match `byte_len`.
- `sha256`: on-disk digests are exactly the pinned `c4f5361c…` and `ea002fa9…`.
- `format` (`validate_default_glyf_font`, `sfnt.spl:153-181`): both start
  `00 01 00 00`; both carry all seven required tables
  (`glyf,loca,head,maxp,cmap,hhea,hmtx`); neither carries any of the excluded
  tables (`CFF `/`CFF2`/`COLR`/`CPAL`/`SVG `/`CBDT`/`CBLC`/`EBDT`/`EBLC`/`EBSC`/`sbix`/`bdat`/`bloc`).
- `tables` (`sfnt_manifest_tables_match`, `sfnt.spl:194-206`): the real
  directories are byte-identical to the pinned manifests -- Bungee 17 tables
  `GDEF,GPOS,GSUB,OS/2,cmap,gasp,glyf,head,hhea,hmtx,loca,maxp,name,post,prep,vhea,vmtx`;
  UnifrakturCook 19 tables
  `DSIG,FFTM,GDEF,GPOS,GSUB,OS/2,cmap,cvt ,fpgm,gasp,glyf,head,hhea,hmtx,loca,maxp,name,post,prep`.
- `names` (`sfnt_manifest_names_match`, `sfnt.spl:447-461`): the decoded
  UTF-16BE name strings in both files match the expected
  `|family|style|full|postscript|version` line character for character,
  including UnifrakturCook's trailing-space version.
- Neither file has an `fvar` table, so `default_axes == "static"` is the
  factually correct catalog value.

So this is not catalog metadata drift against the assets.

## READ-DERIVED, UNVERIFIED root-cause hypothesis

Given the above, the refusal has to come from a code path the 14 accepted
faces never execute. There is exactly one such path in the whole selected-asset
validator: the **no-`fvar` branch** of `sfnt_manifest_default_axes_match`,
`src/lib/common/encoding/sfnt.spl:206-232` --

```
    val has_fvar = match find_table(font, 1719034226):
        Some(_): true
        None: false
    if not has_fvar: return manifest == "static"
```

reached from `validate_glyf_font_instance` (`sfnt.spl:234-239`), whose failure
is mapped to reason `default-axes` at `font_registry.spl:599-602`. Every
variable face returns on the `has_fvar == true` side and never touches this
line; the two static faces are the only callers of it in the guest.

**Primary hypothesis:** on the freestanding native (baremetal) lane the
`has_fvar` probe or the `manifest == "static"` compare does not answer
correctly, so a legitimately static font is refused as
`unsupported-variation-instance`. This file already documents the same
Option-marshalling failure class at `sfnt.spl:170-173` and `sfnt.spl:210-213`
("Option-vs-None `==` is the documented unhealed marshalling sink on the
freestanding native lane"), and both existing comments were written after the
`match` form was *already* required to work around it -- i.e. this exact call
shape has a history of answering wrongly in-guest.

**Secondary hypothesis:** reason `names`. Static fonts have no nameID 16/17
(typographic family/subfamily), so `_sfnt_selected_name` (`sfnt.spl:~316`)
takes its *fallback* ID branch, which the 14 variable faces never take;
UnifrakturCook additionally carries a FontForge-generated Macintosh-platform
name set alongside the Windows one, which stresses the "same name_id seen with
two different values -> valid=false" rule in `SfntNameValue.add`
(`sfnt.spl:241-250`). The bytes match the expected line host-side, but the
in-guest decoder (`_sfnt_utf16be_text` + the file-local `_sfnt_char_from_code`)
is a different implementation path than the host probe used.

Both hypotheses are consistent with all the observed evidence. Nothing here was
executed; do not treat either as established.

## Why this is NOT a desktop-text blocker

The desktop draws with the **default monospace face only**. Since
`acd7196e1d0`, readiness reads `simpleos_desktop_default_font_registered()`
rather than the 16/16 corpus aggregate, and that default face (Noto Sans Mono)
registers correctly -- which is why the same boot now prints `accepted=1` and
`[desktop-gui] font identity=…;raster=pure-sfnt-glyf` where it previously
printed `accepted=0` / `font unavailable fallback=bitmap`. Bungee and
UnifrakturCook are corpus/script-coverage faces (`display` and `blackletter`
category witnesses); their absence costs `catalog_complete=0` and those two
categories, not vector text. The remaining WM rung-(d) blocker
(`reason=dynamic-scanout-or-desktop-readiness-missing`) is downstream of font
registration and unrelated to this.

## Fix recipe

1. **Make the receipt name the reason first.** `validate_selected_font_asset()`
   already computes a precise reason (`byte-length` / `sha256` / `format` /
   `default-axes` / `tables` / `names`) and
   `font_renderer_register_selected_bytes`
   (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:412-435`) throws it
   away by returning a bare `bool`. Thread it through so the serial line reads
   `Bungee=rejected:118996B:default-axes`. This is a one-boot experiment that
   discriminates the two hypotheses above without guessing, and it follows the
   same "a refusal must name itself" principle `acd7196e1d0` established.
2. **If the reason is `default-axes`:** the `has_fvar`/static branch at
   `sfnt.spl:216-219` is the defect site. Give the static case an explicit
   early return before any Option-shaped table probe is consulted (e.g. decide
   `manifest == "static"` first and only probe `fvar` when the manifest is
   non-static), matching the workaround style already used elsewhere in the
   file.
3. **If the reason is `names`:** the fallback-nameID path in
   `_sfnt_selected_name` / the multi-platform `add()` de-duplication is the
   defect site; fix the decoder, not the catalog.
4. **Do not "fix" this by relaxing a gate or editing the pinned catalog.** The
   pinned metadata was confirmed correct against the real bytes above; a
   catalog edit would only hide the parser defect.

## Verification

- Re-run the OVMF-pflash `wm-fullscreen-evidence` lane (source-built kernel)
  and read the `[desktop-gui] font register` line: the fix is proven when it
  reports `catalog_complete=1 registered=16/16 unregistered=` with `accepted=1`
  still set.
- Board-runnable rule applies: the same artifact must be exercised on the
  physical board path, not QEMU only.
- A host-side unit check over the two assets asserting
  `validate_glyf_font_instance(bytes, "static").supported == true` guards the
  static branch against regression, but is NOT sufficient on its own -- the
  suspected defect is lane-specific to the freestanding native backend, so the
  in-guest serial receipt is the authoritative evidence.

## Follow-up: the arm64 mirror of `acd7196e1d0` is still missing

`acd7196e1d0` deliberately did NOT include the identical arm64 change. Its
revert guard found that this working tree's copy of
`examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl` is BEHIND
origin, so committing it would have reverted a parallel session's guest-owned
showcase-animation work. x86_64 got the fix; arm64 did not.

**What x86_64 received** (`arch/x86_64/gui_entry_desktop.spl`):

- readiness now reads `simpleos_desktop_default_font_registered()` instead of
  the whole-catalog aggregate returned by
  `simpleos_desktop_register_selected_fonts_from_vfs()`;
- the serial line carries per-face receipts: `accepted=`,
  `catalog_complete=`, `registered=n/total`, and
  `unregistered=<family=reason,…>`;
- the extra imports from `os.desktop.font_bootstrap`
  (`simpleos_desktop_registered_font_count`,
  `simpleos_desktop_selected_font_count`,
  `simpleos_desktop_font_failure_summary`,
  `simpleos_desktop_default_font_registered`).

The shared `src/os/desktop/font_bootstrap.spl` half already landed and serves
both arches, so arm64 is missing only the entry-file half. Until it lands,
arm64 keeps the mis-scoped gate: one unregistered corpus face still forces the
bitmap fallback on a boot whose default face loaded fine.

**Precondition for doing it safely.** Do NOT apply the diff to the local file
as-is. First reconcile
`examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl` with origin,
and verify by diffing **both directions** -- origin's version may be ahead on
some axes and behind on others, so overwriting either way can revert real work.
Read both the `-` and `+` sides of `diff -u <origin> <local>` before choosing,
then apply the readiness/diagnostic change on top of the reconciled file.
