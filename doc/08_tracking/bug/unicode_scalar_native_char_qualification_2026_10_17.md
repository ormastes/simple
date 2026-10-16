# Checked Unicode scalar conversion qualification

Date: 2026-10-17
Related OPEN bug: BUG-HIR-CHAR-CODEC-NATIVE-BOUNDARY-20261017
See hir_char_codec_native_boundary_2026_10_17.md for actual main fatal witness and generator/version/wire-policy requirements. Database registration remains pending.

This bounded candidate implements only unicode_scalar_to_char(codepoint:i64)->Result<char,text> in a new std.common.encoding.unicode_scalar owner. Existing char_from_codepoint and chr APIs still return text unchanged. The public helper rejects values outside0..1114111 and55296..57343 before the existing generic numeric `as char` cast. No text pointer is cast to char, no new runtime ABI is declared, and actual strict Char constructor admission is unchanged.

Source-supported candidate path: parser_expr recognizes as→expr_cast; parser type fallback preserves named char; HIR types resolves char to HirTypeKind.Char; expression_core emits HirExprKind.Cast; lower_cast_or_convert and MirBuilder.emit_cast preserve the typed target; LLVM Char is i32 and integer conversion uses trunc. All valid Unicode scalars fit i32 without loss. This is not yet an execution proof, and no runtime PASS is claimed.

The shared native/BDD controls call the actual public helper, construct and match the actual canonical HirExprKind.CharLit payload, cast that payload back to i64 and check rendering bytes. They cover ASCII/BMP/nonBMP, NUL/U+0003, escapes, U+FFFD, boundary55295/57344/1114111 and invalid scalars. Large4294967361 and-4294967231 would both narrow to65 if range validation ran after truncation; both must be rejected. i64 maximum also must be rejected. These checks do not use unsupported character literal expressions or array pointer equality.

Public doctests, shared spec, native entry and mirrored manual are UNRUN. NativeChar feature qualification starts at cycle1/3 only after exact source/command review and proper immutable source/runtime/SDK preflight. It does not reuse exhausted generator cycles, spend a reader cycle, or rerun the green factory helper. No generated codec/reader consumer has been qualified by this candidate. Proper codec repair must separately preserve exact version nil-wire policy and strict Unicode decoding, regenerate authoritative output and execute real consumer controls.