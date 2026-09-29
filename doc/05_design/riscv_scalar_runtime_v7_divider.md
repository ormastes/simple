# Runtime scalar pipeline V7: dynamic divide/remainder lane

V7 extends the tag-two stateful M lane from V6 Zmmul to the complete IM
divide/remainder family.  It must replace the V6 multiply-only provider with a
single owner; two tag-two providers must never compete for the same pending
transaction.

## Admission

The plan-bound DIV/REM admission contract is the sole authority for the exact
RV32 rows `DIV`, `DIVU`, `REM`, `REMU`, and for the RV64 word rows `DIVW`,
`DIVUW`, `REMW`, `REMUW`.  A provider captures only a legal tag-two request
whose row, semantic opcode, width flag, form, raw fields, original/canonical
identity, fallthrough, lineage, and event IDs agree.  It normalizes x0 before
capture.  Malformed accepted tag-two traffic latches a protocol fault and never
manufactures an architectural completion.

## Dual geometry

RV64 word operations cannot use an XLEN-width divide graph merely by
truncating inputs: the restore counter, sign bit, special-case value and result
width are all operation-width dependent.  The owner therefore contains two
renamed, fixed-geometry restoring graphs on RV64:

- XLEN graph for normal 64-bit DIV/REM;
- 32-bit graph for `*W` operations.

At request capture the owner stores `word_mode`, quotient-versus-remainder,
signedness controls, normalized magnitudes, original dividend, and special
case selector.  It runs only the selected graph for its fixed width, and muxes
the captured-result path at completion.  The `*W` result is sign-extended to
XLEN only after quotient/remainder selection.  RV32 contains only the 32-bit
geometry.

The normalizer's `row_matched` output is deliberately only a form/row/semantic/
width match.  It must be ANDed with the owner's full tag, decode-legal, class,
memory-effect, original/canonical, raw-register, length, PC, lineage, and event
metadata checks before either request acceptance or protocol-fault authority.

Restoring iterations shift the dividend into the remainder, compare the
candidate remainder against the divisor, conditionally subtract, append the
decision bit to the quotient, and repeat for the captured width.  Architectural
corner results are captured without traps:

- divide-by-zero: quotient all ones, remainder original dividend;
- signed minimum divided by minus one: quotient minimum, remainder zero.

## Completion and integration

The owner holds its full normalized 25-field completion envelope until the
pending owner accepts it.  Memory, trap, and redirect fields are zero; writeback
is suppressed for `rd=x0`.  A V7 flat pipeline/backend is a versioned V6 copy
that substitutes this one tag-two owner while retaining the same public ABI and
the V6 eleven-source fault gate.  Its clocked GHDL evidence must cover normal,
zero-divisor, signed-overflow, x0, backpressure/reset, and all RV64 word forms.

## Implementation handoff

The existing runtime multiply provider is a monolithic `HwSequentialModuleDef`.
The normalizer and restoring-divider graphs are capture-time/transition leaves,
not sequential child entities that can be composed with it. V7 therefore must
implement one flat `runtime_m_provider` with a single tag-two handshake and
completion store; it must not instantiate or route two competing tag-two
owners.

The flat owner needs the multiplier state from V6 plus divider state for the
selected geometry: RV32 has the 32-bit divider state; RV64 has separately
prefixed 64-bit and 32-bit divider state. Capture stores operation kind,
word-mode, normalized operands, sign controls, remainder selection, special
code, and the complete completion metadata. Its priority is protocol fault,
completion consume, multiply finish/iterate, divider finish/iterate, then
request capture. Divide finalization occurs after `count == operand_width`;
it must not borrow the multiplier's `width - 1` terminal convention.

The dedicated owner unit and clocked GHDL evidence are still required before a
V7 pipeline/backend copy is started. Until then V6 remains the integrated
Zmmul-only milestone.

## Required clocked evidence

The isolated owner bench must use the tag-two request/completion ABI and
observe an iterative interval: after a captured request, `request_ready` is
low and `completion_valid` remains low for at least one restore cycle. It must
then hold every completion field stable while `completion_ready=0`, consume
exactly once, and return to ready after that edge.

Required result vectors are:

- RV32 `DIV`, `DIVU`, `REM`, and `REMU`, including signed negative operands;
- each signed and unsigned divide-by-zero rule; signed minimum divided by
  minus one; and x0 base/source and x0 destination normalization;
- RV64 full-width counterparts plus every `DIVW`, `DIVUW`, `REMW`, and
  `REMUW` form, using hostile upper operand bits to prove 32-bit truncation
  and XLEN sign extension;
- malformed tag-two metadata (row/semantic/width/lineage/illegal marker),
  which is accepted only to latch the sticky provider protocol fault and must
  produce no completion; and
- reset while idle, restore-busy, and completion-held.

Every successful completion must prove tag two, no memory/trap/redirect
effects, `rd_write == (rd != x0)`, original/canonical instruction identity,
length four, fallthrough PC, and echoed provider/decode event IDs.
