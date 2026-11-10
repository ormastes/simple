# Foreign-call borrow origin

Bug: `resource_borrow_pinning_not_enforced_2026-08-07`.
Architecture: resource declaration safety invariant 3 (borrow pinning through
foreign calls). This change uses the existing NLL loan and call-wide short
contract machinery; it does not invent a second lifetime solver.

## Declaration authority

`MirOperand.call_origin` distinguishes Source, Runtime, Foreign and Unknown.
The shared schema and generated-runtime producers belong to the runtime-call
origin repair. The foreign-borrow consumer classifies a resolved declaration
through the existing provider metadata: a present true `callable_text_value_abi`
row means a Simple declaration, while a present false row was registered from
an actual extern. Missing metadata yields Unknown. Function spelling, including
an `rt_` prefix, never proves origin. Compiler-owned builtin method tags retain
their Runtime classification.

Source function operands, named references and the direct resolved-call path
carry this authority. Return-signature repair, the admitted file-write ABI alias
and verification-signature normalization preserve it. Generic MIR rewrites and
serialization must preserve the same field; the shared origin repair and MIR
fingerprint lane own those dependencies.

## Borrow behavior

Both instruction calls and call terminators use the existing direct-call
contract checker. Foreign and Unknown targets invoke it in legacy as well as
strict bodies. Only Source callees may consume published local short summaries:
an extern cannot acquire a same-spelled local function's proof by name.

No checked foreign non-retention proof exists in the present summary producer;
parameter effect analysis explicitly labels extern reference/class inputs
`foreign-unknown`. Their live reference arguments therefore record an escape
and produce the existing precise short-contract diagnostic. The compiler does
not assume that returning from an unproved foreign call ends retention.
Scalar foreign arguments with no loans remain valid. Proven local legacy calls
retain their existing behavior. Indirect invocation keeps its existing
conservative contract handling.

This is fail-closed enforcement for unknown foreign retention. It is not runtime
handle retention and does not admit borrowed foreign calls without a separate
checked external proof authority.

## Evidence

`test/01_unit/compiler/resource/foreign_call_borrow_origin_spec.spl` contains
source-to-MIR provider classification and actual NLL assertions for foreign and
local callees, absent provider metadata, local-summary isolation, scalar inputs,
copied aliases, named-reference signature repair and call terminators.

The older `Ref; Drop` fixture without a call is not used as evidence of a foreign
boundary. Existing ordinary move/borrow and lifetime specs remain required
compatibility checks. No runtime PASS is claimed until an actual self-hosted
runner executes these cases with positive counts, followed by the required
compiler/core/MCP checks and integration smoke.
