# Runtime scalar pipeline V8: dynamic Zicsr lane

V8 extends the stateful pipeline with the pending protocol's reserved CSR lane
(tag 3). It is versioned from V6/V7 work and must not mutate the working V6
Zmmul product.

## Provider boundary

`runtime_csr_provider` is a single outstanding, tag-three sequential owner.
It receives only the pending owner's registered decoded-uop payload and returns
one held normalized completion envelope. It exposes the external CSR service
contract:

- lookup request valid and 12-bit CSR address;
- `csr_present` and XLEN `csr_read_value` response inputs; and
- held commit valid/address/value outputs.

The provider captures all request fields atomically. It validates tag, legal
decode, exact plan row/form/semantic/class/effect/declared width, raw rd/rs1/
rs2 fields, original/canonical equality, four-byte length, fallthrough PC,
lineage, and event identity. A malformed tag-three request is accepted only to
latch its sticky provider protocol fault; it never reads or commits a CSR.

The frozen decoder representation for these rows is execution class **6** and
memory effect **3** (`csr`). These are the pending-owner route codes; a CSR
provider must reject class 3/effect 0 rather than treating it as a compatible
memory-style request.

The initial V8 service ABI is deliberately combinational: it has no separate
lookup-ready or response-valid handshake. The provider asserts lookup only for
an admitted request and captures `csr_present`, `csr_read_value`, the policy
result, and derived write intent on its accept edge. It must never consult live
CSR service inputs while a completion is held under backpressure. A pipelined
CSR service requires a separately versioned response-handshake ABI.

Consequently there is no deferred lookup phase in the first owner: request
acceptance captures the old value, access/trap decision, and final commit value
into the one held completion record. `csr_commit_valid` is asserted only for
that record's legal write intent **and** `completion_ready`, so a stalled
completion cannot repeatedly commit. Execute-trap policy failures retain
decoder-legality lineage (`completion_illegal_valid=0`) and use execute cause
2/tval=original instruction.

## Architectural semantics

Admitted rows are `CSRRW`, `CSRRS`, `CSRRC`, `CSRRWI`, `CSRRSI`, and `CSRRCI`.
The old CSR value is the candidate rd value. Register forms use effective rs1
(x0 is zero); immediate forms use zero-extended instruction rs1/zimm bits.

- CSRRW/CSRRWI always request a write.
- CSRRS/CSRRC and their immediate forms request a write only for nonzero
  source/zimm.
- `rd=x0` suppresses only architectural writeback; it does not suppress a
  requested CSR write. A CSRRW/CSRRWI with `rd=x0` may omit an unnecessary old
  value read, while set/clear forms still read the old value.
- absent CSR, inadequate privilege (CSR address bits 9:8), and read-only
  address bits 11:10 with a requested write produce an execute trap/illegal
  completion and no commit.

Completion and commit are held together until `completion_ready`; the commit
fires exactly once on completion consumption. Memory/redirect fields are zero.

## Integration and evidence

A V8 flat pipeline/backend replaces only the CSR typed-zero lane with the
dynamic provider and adds its external lookup/commit ports to the public ABI.
The pending completion envelope and global-fault ownership remain unchanged.

V8 must use a canonical combined profile, `rv32i_zmmul_zicsr_zifencei` or
`rv64i_zmmul_zicsr_zifencei`: base-I, the multiply-only Zmmul subset, Zicsr,
and Zifencei in one ordered decoder plan. It must not accept `rv32im`/`rv64im`
until a unified dynamic DIV/REM provider exists, and it must not pretend that
the Zicsr-only plan includes the live V6 multiply lane. The combined profile is
a prerequisite artifact for V8 construction and provenance.

Clocked evidence must cover all six forms, read-only/privilege/absent faults,
x0 source and destination behavior, completion and commit stability under
backpressure, exact-once consumption, malformed metadata sticky fault, and
reset recovery. V8 is not started until the isolated provider and its test
matrix are complete.

## Flat-owner construction rule

The dynamic owner must be built as one closed sequential graph, not by adapting
the static instruction-specialized CSR owner. Construct its named constants,
signals, per-row admission chain, and policy slices before appending any
operation that references them; every combinational result has exactly one
driver. In particular, derive CSR privilege from the captured canonical
address's bits 9:8 and read-only class from bits 11:10, then validate the
fixed-slice sources and widths in the final module diagnostic. A draft with
deferred lookup, duplicate combinational result drivers, or live CSR service
data after acceptance must be removed rather than integrated.

`HwSequentialModuleDef.child_entity` is not an acceptable way to consume the
capture projection: it creates a child/decoder pin topology rather than the
required single closed owner graph. The provider must inline the same
plan-derived SSA admission/policy schedule under its own request ports, then
assign captured results directly into registers on `request_accept`. The
standalone projection remains the executable contract and regression oracle;
it is not a sequential-child integration shortcut.

Diagnostic closure alone is not acceptance. The per-row select chain must carry
the selected form and immediate bit into all of: source selection, write
requested, set/clear value, read request, and policy capture. It must also
conjoin `illegal_valid==0`, every canonical raw rd/rs1/rs2 binding, and the
full privilege/reserved/read-only policy before producing the captured
completion. Hardwired form controls, hardwired raw-field success, or a policy
that checks only `csr_present` are architectural defects even when the HWIR
driver/width diagnostic is clean.

## Admission projection construction constraint

The standalone admission/policy projection is an implementation prerequisite
for the owner. It must use strict SSA-style HWIR naming: each `HwCombOp`,
`HwCompareOp`, or `HwSelectOp` has a fresh destination signal; reductions and
muxes advance through named stages instead of rewriting a result. In
particular, raw-field proof is `canonical_instruction >> shift_constant`, then
`trunc` to five bits, then `HwCompareOp.equal` to the supplied decoded field
for each of rd, rs1, and rs2. A parser-successful graph with a duplicated
comb/select destination is invalid and must be removed before it becomes owner
input.

The form fold carries six exact form codes: `0=CSRRW`, `1=CSRRS`,
`2=CSRRC`, `3=CSRRWI`, `4=CSRRSI`, `5=CSRRCI`. Its derived controls must be
computed from distinct form predicates, rather than one broad
"immediate"/"set-or-clear" shortcut: immediate is forms 3–5, set is forms 1
or 4, clear is forms 2 or 5, and write-always/read-suppress are forms 0 or 3.
The policy graph also remains staged and single-producer: privilege-sufficient,
current-privilege-not-reserved, required-privilege-not-reserved,
not-readonly-write, then their fresh AND reductions. This is necessary for
CSRRSI/CSRRCI correctness and strict HWIR driver closure.

### Required capture-projection schedule

The projection is driven by `request_handshake`, rather than `request_valid`,
so the combinational CSR service is sampled only on the owner's capture edge.
It accepts the full pending request record plus `csr_present` and
`csr_read_value`. Its minimum outputs are `admitted`,
`protocol_fault_candidate`, lookup valid/address/read-enable, and legal commit
intent/address/value. The future sequential owner registers those outputs on
the same capture edge.

Common checks are fresh signals in this order: tag equals 3; canonical rd,
rs1, rs2 extraction (32-bit shift, five-bit truncation, equality to each
supplied field); original equals canonical; length equals four; provider event
equals decode event; lineage valid; fallthrough equals PC plus four; illegal is
clear; class equals 6; effect equals 3; declared-width is zero. For each exact
plan CSR row at its original one-based index, form, row, semantic, class,
effect, and width comparisons are reduced via fresh `meta01`, `meta23`,
`meta45`, `meta_a`, and `row_match` signals. A fresh row fold carries selected
form, immediate, set, clear, write-always, and read-suppress controls.

Only after the fold may the projection reduce the common gates into
`formed`, then `admitted = request_handshake & tag_ok & formed`; a malformed
tag-three handshake produces `protocol_fault_candidate`. CSR presence,
privilege, and read-only policy are deliberately *not* protocol-malformation:
they produce an admitted execute-trap completion candidate. The policy stage
uses separate current-privilege-reserved, required-privilege-reserved,
privilege-sufficient, read-only-write, and fresh AND-reduction signals.
