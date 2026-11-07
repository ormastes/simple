# Builtin declaration identity controls

Status: AUTHORED / NOT_RUN. Manual companion, not generated execution evidence.

The executable spec allocates real canonical SymbolTable rows and calls the
production registry and TraitSolver APIs. It checks:

- Local/imported shadowing and later ordinary declarations, including a real
  unrelated local ID 1 that must not become builtin Clone.
- Private allocation leaving original containers, counters and scope unchanged.
- Near-i64 exhaustion, negative counters, reserved-ID collision exhaustion and
  the last complete eight-symbol/one-scope allocation window.
- Provider-to-consumer rebinding with different local IDs and stable owner identity.
- Duplicate creation, mutated kind/owner, stale IDs and mismatched solver owners.
- Independent public visibility/public flags on both owner and trait rows,
  plus divergent solver row spans, rejected before any installation mutation.
- Complete prevalidation before solver/associated-type state mutation.
- Exact Copy→Clone and Ord→Eq links, duplicate installation rejection, and no
  automatically installed implementation rows.
- Existing obligation solver rejects an Ord impl without Eq and accepts it
  after the fixture explicitly adds Eq for the same named record.

These controls do not execute generic source programs, select primitive/float
policy, qualify serialized cache transport, or prove compiler entrypoint wiring.
