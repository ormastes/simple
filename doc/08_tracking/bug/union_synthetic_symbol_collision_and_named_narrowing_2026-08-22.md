# Structural union symbol and named-narrowing follow-up

## Status

Open. Static audit on 2026-08-22; no compiler execution was permitted.

## Remaining correctness risks

`union_synth_symbol_id` compresses canonical names into a 100,000,000-value
range and `union_normalize_module` writes directly into `module.enums` by that
ID. A collision can overwrite another synthesized enum. Fixing this requires a
module-owned deterministic name-to-ID registry used by both enum registration
and HIR narrowing; local probing in only one caller would make their IDs differ.

Source narrowing currently maps primitive written names to canonical keys, but
a named source type is returned as its spelling while resolved union members use
symbol-ID/generic-argument structural keys. Named/generic narrowing therefore
needs resolved type identity rather than another textual alias table.

## Completion conditions

- One module-owned registry resolves canonical union names to collision-free IDs
  deterministically and is consumed by synthesis and narrowing.
- Existing enum IDs cannot be overwritten silently.
- Named and generic type-test arms resolve through HIR type identity.
- Collision and named/generic fixtures prove exact enum, variant, payload, and
  diagnostic behavior.
