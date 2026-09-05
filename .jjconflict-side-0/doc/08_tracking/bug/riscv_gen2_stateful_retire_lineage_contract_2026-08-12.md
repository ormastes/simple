# Gen2 Stateful Frontend Needs an Architectural Retirement Producer Contract

Status: open — development-stage product limitation

## Observation

The bounded Gen2 parcel frontend exposes a 64-bit `dispatch_lineage` and
accepts retirement only when `retire_lineage` matches its outstanding entry.
Its generated protocol vectors prove local capture, dispatch, matching
retirement, fault containment, reset priority, and two consecutive tokens.

It is not yet connected to a precise architectural retirement producer. The
local terminal-lineage rule prevents counter wrap and token reuse before reset,
but it cannot prevent a pre-reset stale retirement from appearing after an
uncoordinated frontend reset.

## Safety impact

The frontend must not be presented as a complete processor fetch/dispatch/
retirement path. Its local sticky-fault behavior is fail-closed, but exact-once
retirement ownership and reset-coupling require a core-level contract.

## Required remediation

1. Bind `dispatch_lineage` to the frozen `RetireRecord` producer at the sole
   commit owner, with reset synchrony and ordering assertions.
2. Preserve the terminal-lineage fault rule in the future receipt channel: a
   matching terminal retirement must not wrap or reuse its token.
3. Add composed RV32/RV64 target evidence from parcel capture through decoder,
   dispatch acceptance, retirement record, and reset.

## Unblock evidence

The admitted self-hosted compiler must run the resulting RV32/RV64 VHDL/GHDL
vectors and retain a formal or assertion-based exact-once/ordering receipt.

Owner: RISC-V Gen2 scalar-retirement integration wave
