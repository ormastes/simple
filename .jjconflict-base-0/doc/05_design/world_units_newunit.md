<!-- codex-impl -->
# World Units and Newunit Design

The parser recognizes `newunit Name: Base as suffix` as a standalone nominal wrapper. It rejects `newunit Name = ...` and `newunit name(base: Type): ...`; those remain measurement `unit` forms.

The catalog schema records quantity kinds, unit classes, aliases, provenance, prefix rules, currencies, count/trade units, and derived units. `world_units_v1.sdn` seeds the required first examples: `km`, `kg`, `km/h`, UCUM year variants, `USD`, `piece`, `dozen`, `set`, `mol/L`, `M`, `B`, and `KiB`.

Exact conversions use `ExactRatio` in `world_units.spl`; for example `km/h` has exact factor `5/18` relative to `m/s`. Prefix generation consults `is_prefix_blocked` so accepted non-SI time/calendar units such as `h`, `d`, and year variants are not auto-prefixed.

Migration of public primitives should use `newunit` for nominal values and measurement `unit` only for real quantities. Any remaining raw public primitive must have a local `@allow(primitive_api)` reason.
