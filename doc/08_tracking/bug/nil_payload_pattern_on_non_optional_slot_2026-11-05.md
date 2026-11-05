# nil payload pattern on a non-optional slot (`Some(nil)`, `Ok(nil)`, `Err(nil)`)

- **Status:** FIXED in source (HIR diagnostic), PR work/mirp2-I. P2.
- **Found:** s3_fable43 (phase-3 P1 lead), family I1.
- **Layer:** 20.hir pattern lowering (`expression_components.spl`), MIR fallout.

## Policy decision
`nil` is only the `T?` absence literal (ERR-01). A `nil` sub-pattern therefore
has meaning only when the wrapped payload slot is itself optional:

| shape | slot | verdict |
|---|---|---|
| `Ok(nil)` over `Result<T?, E>` | optional | lowers (17f3f27959e, 606bf9986ac) |
| `Err(nil)` over `Result<T, E?>` | optional | lowers |
| `A(nil)` over `enum E: A(i64?)` | optional | lowers |
| `Some(nil)` over `i64?` | `i64` (non-optional) | **HIR error** |
| `Ok(nil)` / `Err(nil)` over a non-optional slot | non-optional | **HIR error** |

`Some(nil)` is not a lowering gap: it can never match, so it is now a clean
diagnostic: "`Some(nil)` can never match: the Some payload is not optional
(nil is only the T? absence literal); match absence with `case nil:` ...".

## Before
- MIR: generic "enum match: nil sub-pattern requires a declared optional payload slot".
- Seed JIT (`bin/simple.exe run`): `opt_kind(Some(4))` with `case Some(nil):`
  first returned `"some-nil"` -- the arm was silently TAKEN (wrong answer).

## s3_fable43 note
The `Err(nil)`/`Ok(nil)` failures over genuinely optional slots reproduce only
on binaries predating 17f3f27959e / #6943 (s3_fable43 relinks old objects).
Current source lowers them cleanly (spec below). Native qualification of the
nested `Ok(Some(chunk))` text-binder case stays with
`native_enum_nil_payload_pattern_2026_10_11` / PR #6943.

## Specs
`test/01_unit/compiler/50.mir/family_i_nil_payload_and_generic_static_ctor_spec.spl`
(4 accept + 3 reject cases; the 3 rejects were RED before the fix).
