<!-- codex-impl -->
# World Units and Newunit Requirements

REQ-WUN-001: `newunit Name: Base as suffix` shall declare a nominal ABI-transparent wrapper with postfix literal support.

REQ-WUN-002: `unit` shall remain the syntax for measurement families and derived measurement expressions.

REQ-WUN-003: The world-units catalog shall store quantity kinds, unit classes, aliases, exact relationships, and provenance in SDN.

REQ-WUN-004: Derived units such as `km/h` shall be represented compositionally with exact rational conversion factors.

REQ-WUN-005: Calendar years shall distinguish UCUM variants `a`, `a_j`, `a_g`, and `a_t`; generic `year` shall not be canonical.

REQ-WUN-006: Currency units shall use ISO 4217 identities such as `USD`; display symbols such as `$` are aliases.

REQ-WUN-007: Public bare primitive APIs shall be migrated to custom `newunit`, measurement `unit`, enum, Option, or Result types unless explicitly allowlisted.
