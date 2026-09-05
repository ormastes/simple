# Runtime scalar pipeline V6: Zmmul lane

V6 preserves the V5 public ABI while enabling the plan-bound, stateful Zmmul
multiply lane.  It is deliberately a new product version: V5 continues to
disable the pending tag-two lane and its ten-source fault gate remains frozen.

## Ownership

The single decoded-uop skid remains the only instruction owner.  The V6 class
router classifies legal class `4` work as a pending transaction with provider
tag `2`.  The pending owner captures the full decoded envelope before the
dynamic multiply provider accepts it, so subsequent live inputs cannot alter
the operation.  The provider holds its normalized completion until the pending
owner accepts it; the completion merge and completion skid then retain the
public completion under downstream backpressure.

The provider admits only exact plan rows for `MUL`, `MULH`, `MULHSU`, `MULHU`,
and RV64 `MULW`.  It validates row, semantic opcode, form, metadata, lineage,
raw register fields, and PC lineage.  Its shift/add engine derives the unsigned
full product, applies signed-high correction when required, and sign-extends
the RV64 32-bit result for `MULW`.  Divide and remainder rows remain unsupported
in V6 and fail closed at the tag-two boundary; V6 is a Zmmul enhancement, not a
claim of full M extension support.

## Fault and reset

V6 replaces V5's ten-source fault gate with an eleven-source variant including
`muldiv_fault`.  Any raw or sticky fault suppresses admission, public
completion, bus, and fence handshakes until the common synchronous reset clears
the sequential fault owner and all registered providers.  The dynamic multiply
provider has no external request side effect, so reset cancels its outstanding
calculation and held completion.

## Evidence

The direct V6 graph validates typed endpoint direction, width, single-driver
closure, all child inputs, all public input use, all public output drivers, and
canonical structural identity.  The strict VHDL renderer publishes the V6
graph and every child hash, including the multiply provider.  Clocked GHDL
scenarios cover RV32 `MUL`/`MULH`, RV64 `MULW`, tag-two latency, held completion,
orphan response faulting, and reset recovery.  Pure-Simple qualification remains
separate from these focused artifacts and requires an admitted current runtime.
