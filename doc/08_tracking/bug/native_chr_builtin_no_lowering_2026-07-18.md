# `.chr()` / `.to_char()` builtin has no working native-lane lowering (empty string on compiled/baremetal path)

- **Date:** 2026-07-18
- **Area:** compiler / 50.mir method lowering (cranelift native lane)
- **Severity:** high (silent wrong result, no diagnostic)
- **Status:** open — workaround landed, compiler fix pending

## Symptom
`val cp: i64 = 65; val s: text = cp.chr()` compiles without error on the
native lane (stage3 self-hosted, `--backend cranelift`) but yields the empty
string at runtime. In-guest micro-probe on SimpleOS x86_64:

```
[desktop-gui] chr-probe chr='' cat='' len=0
```

The interpreter lane implements it correctly
(`10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:883`).

## Impact (observed)
- SimpleOS font validator failed `reason=names`: SFNT name-table UTF-16BE
  decode built every string from `.chr()` pieces → all names decoded empty
  (`font names decoded=|||||`) although the full 1,708,408-byte TTF was read
  and byte-length/sha256/glyf/tables stages all passed in-guest.
- `_vfs_bytes_to_text` (4 copies: vfs_init, vfs_boot_init, vfs_dispatch,
  vfs_write_ops) produced empty text from byte buffers → empty manifests.

## Evidence
- Kernel ELF (655-file fresh build by stage3 `6faa17db…`): no direct or
  indirect call target for any chr-like symbol at the probe site; the only
  `char_from_code` call is the string_core wrapper calling its own inline
  twin. `rt_string_starts_with` (analogous FuncPtr-const lowering) IS present
  and referenced — the mechanism itself works; `.chr()` simply never emits it.
- A lowering was added at
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1491`
  (route unresolved `.chr()`/`.to_char()` → `rt_char_from_code`), stage2+3
  rebuilt fresh (715 compiled / 0 cached), and the kernel probe STILL prints
  empty — i.e. for a **typed i64 receiver** `resolution` is apparently not
  `Unresolved`, and whatever resolved path it takes emits no call and yields
  a zero/empty value. Root of the resolved-path behavior still to be traced
  (host repro `scratchpad/chrtest/chrtest.spl` builds a typed + untyped case).

## Workaround (landed 2026-07-18)
Route all kernel-path call sites through pure-Simple
`string_core.char_from_code` (ASCII table indexing, already proven in-kernel
by the sfnt tag-name path):
- `src/lib/common/encoding/sfnt.spl` `_sfnt_utf16be_text`
- `src/os/services/vfs/{vfs_init,vfs_boot_init,vfs_dispatch,vfs_write_ops}.spl`
  `_vfs_bytes_to_text` (+ the read-file text path in vfs_init)
- probe in `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`
  now prints both `chr='{…}'` (builtin) and `cfc='{…}'` (workaround).

Note `char_from_code_inline` covers ASCII 32–126 + \t\n\v\f\r only; non-ASCII
codepoints decode to "". Sufficient for SFNT name matching and 8.3/FAT text,
NOT a general Unicode chr replacement.

## Sibling defect: native-lane `.replace` replaces only the FIRST occurrence
In-guest proof (same probe run): `"Noto Sans Mono".replace(" ", "")` returned
`NotoSans Mono` (one space left). Interpreter semantics = replace ALL
(`str_replace_all`). This made `_font_candidate_embedded_postscript_name`
compute a wrong expected PostScript name, so `sfnt_manifest_names_match`
correctly failed with reason=names even after the decode side was fixed —
serial line `font names expected-runtime=|…|NotoSans Mono-Regular|…` vs
decoded `…|NotoSansMono-Regular|…`. Worked around in font_registry with
primitive char-extraction stripping; the builtin needs an all-occurrences
native lowering (rt_string_replace appears to be single-shot).

## Related perf blocker (repro attempt)
The minimal host repro could not complete: `stage3 native-build --backend
cranelift --runtime-bundle simple-core --mode dynload` on a 7-line entry spun
**39+ min at 100% CPU with zero objects written** to a fresh cache-dir before
being killed. Tiny-entry native-build is effectively unusable for micro
repros — separate perf bug worth its own investigation.

## Proper fix (todo)
Trace what `resolution` becomes for a typed scalar receiver calling a
runtime-builtin-only method name, and either (a) make HIR leave it
`Unresolved` so the 50.mir fallback fires, or (b) add an explicit typed-lane
lowering to `rt_char_from_code` / `string_core.char_from_code`. Then remove
this workaround note and, optionally, revert call sites to `.chr()`.
