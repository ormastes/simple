# Flat enum parser drops named payload field defaults

Status: source-proven transport omission; runtime reproduction NOT EXECUTED.
Bug DB reconciliation pending: no callable bug DB writer is available here.
Diagnostic overlay introduced in commit `91f3dc186fac2bc45acfbaf45899324aee0e7712`.

Input: `enum E: Named(count: i64 = 9)` using the normal indented enum body.

In `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`, the enum
payload loop records only field names and type tags. Tokens that do not start
another type are advanced over. The final `decl_enum_def` call carries variant
discriminants, flattened payload types/counts, and field names, but carries no
field-default expression slot. Consequently a field default cannot reach the
flat-AST bridge through this representation. This is separate from a variant's
own explicit discriminant after the closing parenthesis.

The archive enum diagnostic must not claim that this parser spelling preserves
defaults. To isolate the existing rich HIR/artifact contract, it can construct a
named HirField default from a genuinely parsed integer-literal function body,
then project that actual HIR graph. Such a documented diagnostic overlay tests
artifact preservation only; it does not fix or qualify parser support.

A production repair must extend the enum payload transport and bridge together,
then verify that parsing, HIR lowering, artifact projection, and named enum
construction preserve/apply the declared default. Do not silently discard the
syntax or infer success from the absence of parser diagnostics.

Recovery for the diagnostic: after parser transport is repaired and verified,
remove `fixture_with_named_default`, restore the intended declaration
`Named(packet: Packet, count: i64 = 9)`, and retain the exact-default artifact
assertion. Until then the overlay uses the actual parsed `default_count` body
before hashing/projecting the modified HIR graph; it grants no parser PASS.
