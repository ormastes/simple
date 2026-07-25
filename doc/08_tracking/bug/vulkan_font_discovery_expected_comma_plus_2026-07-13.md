# Vulkan font discovery parse failure: expected comma, found plus

## Status

Rust seed parser source fixed 2026-07-15; focused regression added, execution
pending. The pure-Simple parser was already correct: expression casts use
`parser_parse_type`, while union-aware parsing is limited to declaration type
positions through `parser_parse_type_with_union`. The Vulkan source workaround
may remain because it is explicit and harmless.

## Root cause (found via bisection, 2026-07-13)

The parser mis-parses `EXPR as TYPE <infix-op> ...` when `<infix-op>` is `|`
(and separately `<` — see the sibling bug in
`parser_sfnt_glyf_expected_comma_found_plus_2026-07-13.md`). After `as TYPE`
the parser appears to speculatively continue parsing a **type expression**
(union type `TYPE | TYPE2` / generic argument list) instead of closing the
cast and resuming binary-expression parsing. When the right-hand operand is
itself an indexed expression like `bytes[off + 1]`, the type-expression parser
chokes on the arithmetic `+` inside the brackets with "expected Comma, found
Plus" (mirroring the known `identifier[expr]`-read-as-generics defect in
`parser_array_index_misread_as_generics_2026-06-14.md`).

Confirmed isolated repro:
```simple
val a = bytes[off] as u32 | ((bytes[off + 1] as u32) << 8)  # fails to parse
val a = (bytes[off] as u32) | ((bytes[off + 1] as u32) << 8) # parses fine
```
Parenthesizing the cast (`(EXPR as TYPE) | ...`) removes the ambiguity because
the parser closes the cast at `)` before ever reaching the `|`.

## Source fix (2026-07-15)

The Rust postfix cast parser now uses `parse_single_type()` instead of
union-aware `parse_type()`. A following `|` therefore remains available to the
binary-expression parser. The focused AST regression uses the isolated repro
above and requires an outer `BitOr` whose left operand is a cast to `u32`.

## Workaround applied

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl`,
`_vulkan_font_bytes_to_pixels`: parenthesized the first cast in the pixel
decode expression:
```
-        pixels[i] = bytes[off] as u32 | ((bytes[off + 1] as u32) << 8) |
+        pixels[i] = (bytes[off] as u32) | ((bytes[off + 1] as u32) << 8) |
             ((bytes[off + 2] as u32) << 16) | ((bytes[off + 3] as u32) << 24)
```
No other `as TYPE |` occurrences remain in this file
(`grep -n 'as [a-zA-Z0-9_]* |'`). This unblocks module load of
`backend_vulkan_font.spl` from `examples/06_io/ui/graphics_2d_showcase.spl`;
the showcase now proceeds past this parse error (it currently stops on an
unrelated 10s example-runner timeout, tracked separately).

The current source subsequently split the byte casts and shifts into named
locals before combining them. That equivalent workaround does not need to be
reverted now that the parser source is fixed.

## Resolution boundary

The `|` ambiguity is fixed by making `as TYPE` close after one type. The
separate `<` ambiguity remains tracked by
`parser_sfnt_glyf_expected_comma_found_plus_2026-07-13.md` and is not claimed
fixed here.

## Prior investigation (unresolved as of first filing)

Open (superseded by the root cause above). This blocks the rebased SimpleOS WM/Web DrawIR production build before
the merged executor is compiled or QEMU starts.

## Evidence

The canonical self-hosted compiler reports:

```text
Build failed: failed to parse .../backend_vulkan_font.spl during discovery:
Unexpected token: expected Comma, found Plus
```

The failure reproduced in two builds using the existing native cache and once
using a brand-new `native-cache-remote-merge-v2`; therefore it is not a cached
discovery failure. The wrapper exits with `wm-simple-web-build-failed` and the
guest serial log remains empty.

Rewriting `atlas_bytes + framebuffer_bytes + (if params_allocated: ... else:
0)` into a statement-level conditional did not change the diagnostic, proving
another `+` token in this newly fetched remote module triggers the older staged
parser. The discovery diagnostic currently omits line/column information.

Recovery on 2026-07-13 explicitly selected
`build/bootstrap-wm/stage3/aarch64-apple-darwin/simple`. Three bounded
production build/fix cycles failed with the same location-free diagnostic.
Temporarily eliminating every `+` token introduced by the font-evidence commit
also did not move the failure; that experiment was reverted. The blocker is
therefore not the compact resource-total expression or the newly added upload
counter increments.

## Next bounded step

Run a parser-only reduction of `backend_vulkan_font.spl` to locate the first
unsupported expression without invoking QEMU. Likely candidates are multiline
bitwise expressions containing indexed `off + N` operands or another compact
expression form introduced after the staged compiler was built. Fix the grammar
if the form is intended Simple syntax; otherwise rewrite only that expression
and then run one fresh production build/QEMU cycle.
