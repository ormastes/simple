# Bug: mutating method call two struct-field hops from `self` silently loses the write (self-hosted binary)

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (silent state loss; systemic for ECS-style services)
- **Found by:** SimpleOS harden lane P4 (TTY), reproduced in isolation

## Symptom
`self.world.output_bufs.insert(...)` — a mutating method invoked on a value
reached through TWO field hops from `self` — executes without error but the
mutation does not persist in `self.world.output_bufs`. One-hop mutations
persist. Reproduced with a minimal standalone repro by the lane (see
`.spipe/simpleos_harden_p4_tty/state.md`).

## Scope
- Observed on the self-hosted binary lane (`build/native_probe/simple`).
- Pre-existing: already silently affecting `tty_create`'s component stores and
  the pre-existing `tty_service_spec.spl` before this session's edits.
- Likely affects every ECS/ComponentStore-style SimpleOS service that mutates
  `self.<world>.<store>` chains — same value-copy semantics class as
  "arrays are value types" but here the intermediate struct copy is silent.

## Workaround (used in `src/os/services/tty_service.spl`)
Extract-mutate-writeback:
```
var s = self.world.output_bufs
s.insert(...)
self.world.output_bufs = s
```

## Next step
Root-cause in the self-hosted compiler's place/lvalue lowering for chained
field receivers of mutating methods; add a regression spec with the minimal
two-hop repro. Related class: value-type copy on method receiver chains.
