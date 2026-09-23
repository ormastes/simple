# Typed array push tails become native traps

Status: fix proposed; native red reproduced; green and compiler-suite validation pending.

## Trigger and cause

The provider-query admission runner from PR #1414 links59 modules but traps
with SIGILL in `src__os__smf__provider_query_wire___push_u32_le +580`.
The helper ends in `out.push(byte)` without a return annotation. An isolated
one-module fixture reproduces exit132 using the admitted Stage2 produced from
source70748fd0, SHA256
`7f6283bc9a2b7e9d7ef7078b5c3bc7fbba49a54d3d6b61f83bb3cd0540a55821`.
This is diagnostic producer evidence, not current-main admission.

The explicit `native-build --entry` command delegates to that binary's embedded
Rust backend. Current main20e17461 still contains the defect:

- HIR treats an array push tail as a value-producing expression, correctly
  retaining the existing implicit return semantics.
- MIR's specialized statement path emits typed u8/u32/u64 push and then clears
  `last_expr_value`. The same operation in expression position returns its
  receiver, because the runtime push helper's Boolean success is not the
  language expression result.
- Non-unit function finalization has no tail result and leaves the block
  `Unreachable`; Cranelift emits `udf #0xc11f`.
- Capacity-backed arrays can additionally be erased by dead-append analysis
  before their tail expression is lowered.

## Fix and acceptance

Preserve the receiver as the typed statement's expression value, using the
existing return coercions. Preserve the runtime call's discarded Boolean
destination and every bounded append/store optimization. Exclude only arrays
referenced by non-unit implicit return tails, including terminal conditional
arms, from dead-append elimination. Keep HIR inference and missing-value
fail-closed backend behavior intact; do not annotate application helpers as
a workaround.

Regression coverage includes u8/u32/u64, push/append, inferred/declared array
returns, explicit unit procedures, and capacity-backed direct/conditional
tails. The native fixture consumes returned arrays, checks mutation, and checks
one evaluation of the push argument. Existing ignored-append elimination tests
must continue passing. No additional runtime allocations or calls are added
to a correctly typed tail; only its already-computed receiver remains live.

## Evidence boundary

Native red built1 module,0 cached,0 failed in2.7s with strict no-stub policy,
jobs1, private cache, and sampled tree limit5859375KiB. Build peak187600KiB;
execution peak2416KiB,exit132; both observer errors0 and quiescent1. The current
fixture adds returned-value and once-only assertions after that initial red;
the initial failing source is retained separately in local evidence.

Evidence directory:
`/Users/ormastes/simple-tmp/statement-helper-unit-return-20260923/build/typed-array-push-tail/`.
No general compiler suite, Stage2 replacement, Phase2, bootstrap, cross-host,
or release PASS is claimed. Independent Astra review and a bounded private
seed/compiler build are required before runtime acceptance.
