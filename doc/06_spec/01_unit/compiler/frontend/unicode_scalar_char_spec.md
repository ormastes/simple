# Checked Unicode scalar native character

Executable spec: test/01_unit/compiler/frontend/unicode_scalar_char_spec.spl
Shared controls: unicode_scalar_char_fixture.spl
Native entry: unicode_scalar_char_native.spl
Status: UNRUN; source/manual only, no execution evidence.

The actual std.common.encoding.unicode_scalar.unicode_scalar_to_char function validates integer range and rejects surrogate scalars before the existing numeric cast. Controls use the actual HirExprKind.CharLit constructor, qualified payload match and numeric cast-back; they check exact text/UTF-8 bytes for ASCII, BMP, supplementary-plane, NUL, U+0003, newline, backslash, U+FFFD and valid scalar boundaries. Invalid bounds/surrogates and large positive/negative values that would truncate to ASCII must return the exact denial reason.

BDD and standalone nonzero native main call the same exported helper. No character literal expressions, fixture-generated Char layout, fake FFI signatures or generated-codec consumer claims are involved. A future successful probe qualifies this checked primitive only; the OPEN HIR character codec bug remains documented separately. NativeChar feature cycle1/3 has not started. Reader factory controls are not rerun.