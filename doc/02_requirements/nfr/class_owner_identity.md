# P3 nonfunctional requirements

- Identity lookup uses the existing qualified dictionaries; constructor use
  does not scan provider modules or swap SymbolTables.
- Default relocation is linear in the default expression tree. Repeated type
  and callable identities reuse consumer-qualified bindings.
- Provider tables are temporary preparation inputs, not stored per class or
  field. Retained expression/type/link maps participate in transient ownership.
- Measure real elapsed time and peak RSS with an admitted self-hosted runtime.
  The current campaign has no such runtime, so these measurements and branch
  coverage are pending; no numeric performance target is claimed satisfied.
