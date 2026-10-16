# Checked Unicode scalar native character

Executable spec: test/01_unit/compiler/frontend/unicode_scalar_char_spec.spl
Shared controls: unicode_scalar_char_fixture.spl
Native entry: unicode_scalar_char_native.spl
Status: focused native controls FAIL in final cycle3/3 at NUL rendering; BDD and doctests UNRUN. Actual failure evidence follows.

The actual std.common.encoding.unicode_scalar.unicode_scalar_to_char function validates integer range and rejects surrogate scalars before the existing numeric cast. Controls use the actual HirExprKind.CharLit constructor, qualified payload match and numeric cast-back; they check exact text/UTF-8 bytes for ASCII, BMP, supplementary-plane, NUL, U+0003, newline, backslash, U+FFFD and valid scalar boundaries. Invalid bounds/surrogates and large positive/negative values that would truncate to ASCII must return the exact denial reason.

BDD and standalone nonzero native main call the same exported helper. No character literal expressions, fixture-generated Char layout, fake FFI signatures or generated-codec consumer claims are involved. A future successful probe qualifies this checked primitive only; the OPEN HIR character codec bug remains documented separately. NativeChar feature completed final cycle3/3 with a failure; no further native attempt. Reader factory controls are not rerun.
## Final qualification outcome: FAIL3/3 — 2026-10-17

Tested code frozen699c44fd5a099c9b956dd9142b65da3d102069ba. Final build exited0 with selected parse closure86, parse30/30 workers, HIR16/16 workers/no failures and79 genuine selected SPL objects/capsules. All79 selected paths were new versus the prior selected-object manifest; actual frontend/HIR cache-hit telemetry and successful MIR module total were not recorded and are not inferred. Same original persistent cache, exact producer/runtime lineage and all prior evidence were preserved.

The independently reviewed strict no-FORCE link used those79objects +38 own-D9 C objects with391 current source/header/compiler hash proofs, canonical /MD entry and13 actual init roots. Strict link0/log0. Candidate SHAFC09D528CA0B2FC4C058E5EA00EEB4E846F46BBF3D93AC993DA99BB6A2B9ED40 FAILED its FIRST/ONLY invocation: exit1, exact stdout `FAIL unicode-scalar-char: rendered byte length 0` plus newline49bytes, stderr0,0.025225seconds, unchanged pre/post hash.

ASCII65/BMP233/nonBMP128512 scalar, actual HirExprKind.CharLit payload and rendering controls passed sequentially. NUL scalar/payload cast-backs passed0, then its rendered byte length failed. U+0003, later escapes/boundaries and invalid-input controls were NOT REACHED. See native_char_nul_interpolation_2026_10_17.md for actual COFF/runtime-map proof that raw C-string interpolation concat loses NUL length. The numeric byte conversion workaround fixed the earlier ASCII comparison failure sufficiently to expose this separate real blocker; no global compiler fix is claimed.

Native work STOPPED after feature cycle3/3; no fourth build/run, fixture weakening or budget relabel. BDD/doctests, complete Unicode primitive qualification, generated codec/real reader consumers and broad compiler/lib/MCP/LSP/admission remain unqualified. Existing code at699c44 remains unchanged; this update is documentation only. The earlier proposed8154 indentation defect was caught before any build, corrected to the original loop indentation at699c44, and retained with explicit inverse/indentation evidence.