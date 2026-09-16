# Option payload extraction via `val x = match opt: Some(v): v` yields nil on freestanding native lane

- Date: 2026-08-04
- Lane: freestanding x86_64-unknown-simpleos (cranelift native build, OVMF boot),
  stage3 self-hosted compiler `build/bootstrap/stage3/aarch64-apple-darwin/simple`
- Symptom: `runtime error: field access on nil receiver`, fault
  `rip=0x0000000008073034` → `lib__common__encoding__sfnt__parse_fvar_axes`,
  gate `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` verdict
  `simpleos_wm_fullscreen_status=fail reason=guest-render-fault`
- Serial evidence: `build/simpleos_wm_fullscreen_evidence/serial.log` — pinned
  variable font loaded fine (`[vfs-init] file chain read complete ...
  bytes=1708408`, NotoSansMono[wdth,wght].ttf), then faulted in fvar parsing.

## Root cause (disassembly-proven)

Source shape (src/lib/common/encoding/sfnt.spl, pre-fix line 77):

```
val maybe_table = find_table(font, 1719034226)
val table = match maybe_table:
    Some(value): value
    None: return []
val base = table.offset as i64      # ← faulted here
```

`llvm-objdump -d --triple=x86_64-unknown-none` of the kernel ELF at
`parse_fvar_axes` (0x8072e20) shows the val-assigned match compiled to two
indirect discriminant-check calls (helper 0x800e2b0, selectors 0xf1987159 and
0x8d5e0359) with a **fall-through default that loads the nil sentinel 0x3**
into the `table` slot when the scrutinee matches neither variant
(0x8072f18: `movl $0x3, %eax`). At runtime on the boot lane the Option
returned by `find_table` (a `Some` — the same font passes the
`has_fvar` statement-match in `validate_default_glyf_font` moments earlier)
matched neither check, `table` became 0x3, and the first field read
`table.offset` (`movl 0x8(%rsi)`) tripped the nil guard → ud2 at 0x8073034,
exactly the reported fault RIP.

Key contrast: the *statement-form* matches on the identical
`Option<OtTable>` values in `validate_default_glyf_font` (lines ~133/142/145,
`Some(table): ...` / `Some(_): ...`) executed correctly on the same boot; and
the identically-shaped `val font = match parse_offset_table(blob): Some(v): v`
(`Option<OtFont>`) also worked. Only this `Option<OtTable>`
extraction-into-`val` site mis-discriminated. So this is a codegen defect in
the value-position match lowering for Option payload extraction on the
freestanding lane, not a general Option breakage — same family as the known
"Option None-discrimination → Some-arm-with-nil" class
(doc/08_tracking/bug/ 2026-07-18 baremetal defect catalogue) but a distinct
site: here the compiled default path itself substitutes nil instead of
trapping on an unmatched variant.

Host lanes (interpreter, hosted native) parse this same font correctly.

## Workaround landed (pure Simple, behavior-identical on host)

src/lib/common/encoding/sfnt.spl:

1. `parse_fvar_axes`: replaced the Option match extraction with an inlined
   Option-free flat scalar scan of `font.tables` (found flag + i64
   offset/length), per the proven "flat APIs, no Option across the boundary"
   pattern.
2. Same fn: duplicate-axis check `for axis in axes:` → indexed `while` with
   typed locals (struct for-in iteration variables are a documented broken
   class on this lane).
3. `sfnt_manifest_default_axes_match` (next on the same boot path):
   `find_table(...) == None` → statement match (Option-vs-None `==` is the
   documented unhealed sink), and `for axis in axes:` → indexed `while` with
   typed locals.

## Repro / verification

```
BUILD_DIR=build/simpleos_wm_fullscreen_evidence \
REPORT_PATH=doc/09_report/simpleos_wm_fullscreen_evidence_2026-08-04.md \
SIMPLE_BIN=build/bootstrap/stage3/aarch64-apple-darwin/simple \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Before fix: `simpleos_wm_fullscreen_status=fail reason=guest-render-fault`,
fault rip 0x8073034 in parse_fvar_axes.
After fix: see the 2026-08-04 gate report/serial log (this doc is filed with
the source-shape fix per the CLAUDE.md rule: workaround landed AND compiler
bug recorded — the value-position Option match lowering still needs a real
compiler fix; until then this shape must not be reintroduced in
freestanding-lane code).
