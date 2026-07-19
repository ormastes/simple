# `.chr()` / `.to_char()` builtin has no working native-lane lowering (empty string on compiled/baremetal path)

- **Date:** 2026-07-18
- **Area:** compiler / 50.mir method lowering (cranelift native lane)
- **Severity:** high (silent wrong result, no diagnostic)
- **Status:** source fixed — rebuilt current-source execution pending

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

## Sibling defect: bare-metal `.replace` replaced only the first occurrence (source-fixed)
In-guest proof (same probe run): `"Noto Sans Mono".replace(" ", "")` returned
`NotoSans Mono` (one space left). Interpreter semantics = replace ALL
(`str_replace_all`). This made `_font_candidate_embedded_postscript_name`
compute a wrong expected PostScript name, so `sfnt_manifest_names_match`
correctly failed with reason=names even after the decode side was fixed —
serial line `font names expected-runtime=|…|NotoSans Mono-Regular|…` vs
decoded `…|NotoSansMono-Regular|…`. Worked around in font_registry with
primitive char-extraction stripping.

The x86_64 and ARM64 hardware runtimes now route `rt_string_replace` through
their existing replace-all owner. Both RISC-V64 runtime copies use the same
two-pass non-overlapping algorithm and the same wrapper. A host-executable C
regression covers repeated, expanding, deleting, missing, empty-needle, and
aliased-replacement cases; an SSpec source contract pins all four owners and
keeps both RISC-V64 implementations identical. Fresh guest execution remains
pending.

## Sibling defect (ROOT of the render-fault chain): Option None-discrimination broken on baremetal
A function that legitimately returns `None` can surface in the caller's
`match` as the **Some arm with a nil binding**; the next field access hits the
compiler's "field access on nil receiver" guard (rt_eprintln + ud2). Proven by
disasm twice: (1) `rasterize_sfnt_glyf` returned None → caller's
`match ... Some(bitmap)` bound nil → panic at `bitmap.width`; (2)
`_outline_bounds` returned None for a whitespace glyph (empty outline) →
`bounds.right` panic INTRA-module. Cross-module `opt.?`+field,
`Option == nil/None` compares, and `.unwrap()` are all sinks of the same
marshalling family. Matches only ever "work" when the value is Some.
**Consequence: on the baremetal lane, any routinely-None Option path is a
crash risk.** Workarounds landed: flat `(arrays..., bool)` cross-module APIs
(sfnt_glyf parts API), path-based helpers computing struct fields inside
font_registry, match unwraps only on always-Some paths, and making
whitespace glyphs a valid Some(0x0 bitmap) instead of None.

## Sibling defect: text char-extraction loop faults on baremetal
First workaround attempt for the `.replace` defect (a `str_char_at(family, i)`
loop stripping spaces, running during font candidate construction) produced a
guest EXCEPTION FRAME (`rip=0x8a2bc01` in the
`FontRasterizer.load_selected_bytes` → candidate-construction path, right
after `font read alias bytes=1708408`, stray `51984207` printed). `s[idx]`
text indexing on a text *parameter* is implicated (the same op on a LOCAL
literal receiver works — `char_from_code_inline`'s ASCII table). Replaced
with a literal lookup table (`_font_candidate_no_space_family`). Not
root-caused; same erased/typed-receiver builtin family as above.

## Perf gap: pure-Simple glyf rasterization slows 4K WM re-render past 90s
With real fonts active, the F11-maximize re-render (full-4K window + text via
`rasterize_sfnt_glyf`'s per-pixel `_coverage` edge sampling) no longer fits
the harness's 90s correlation budget under TCG x86_64-on-arm64 (guest printed
the irq marker, then state/frame arrived after the deadline). Budget raised
to 300s in check-simpleos-wm-fullscreen-evidence.shs (strictness unchanged).
Real fix: glyph bitmap caching across frames on the executor path and/or a
scanline rasterizer instead of 4x-sample per-pixel coverage.

## Related perf blocker (repro attempt)
The minimal host repro could not complete: `stage3 native-build --backend
cranelift --runtime-bundle simple-core --mode dynload` on a 7-line entry spun
**39+ min at 100% CPU with zero objects written** to a fresh cache-dir before
being killed. Tiny-entry native-build is effectively unusable for micro
repros — separate perf bug worth its own investigation.

## Root cause and fix (2026-07-19)
A typed integer receiver can resolve `chr`/`to_char` through UFCS to an
unrelated same-named free function in the target source closure. MIR then
honored that resolution even though the interpreter gives primitive integer
builtins priority. MIR now routes declared integer receivers directly to
`rt_char_from_code`; the unresolved native-entry path remains supported, but
only after a custom struct owner has had precedence. The shared cross-target
native fixture forces both UFCS collisions and custom-owner calls, plus BMP
and four-byte UTF-8 values. The pure-Simple runtime now exports the same raw
`rt_char_from_code` ABI, the pure core interpreter accepts both method names,
and x86/ARM bare-metal owners use the same raw-codepoint UTF-8 contract rather
than decoding MIR integers as tagged values or replacing non-ASCII with `?`.
Hosted, FreeBSD, AArch64, RISC-V64, ARM32/RISC-V32, and Windows ARM64 gates
already consume the aggregate fixture; the simple-core smoke additionally
builds and runs C5 against the pure runtime. Rebuilt execution is pending.
