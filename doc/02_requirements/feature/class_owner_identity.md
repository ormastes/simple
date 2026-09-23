# P3 class owner identity

Scope: the requested common-Windows P3 lane. These acceptance criteria are
the existing task selection, not a new feature-options proposal.

- REQ-001: classes with equal source names and different defining modules have
  different canonical identities. Local aliases and reexports retain that owner.
- REQ-002: constructors, nested fields, defaults, instance/static methods, and
  impl/Self use the same owner. Legacy raw composite layout keys remain aliases.
- REQ-003: flat bootstrap visits provider classes before active-module type
  registration. Provider numeric SymbolIds never become consumer bindings.
- REQ-004: recursively relocate Named types and supported default expressions.
  Unsupported captures produce a fatal error when the default is used; explicit
  field arguments and unused defaults do not trigger that error.
- REQ-005: callable definitions, direct calls, and function values agree.
  Extern, export, @global, and the actual entry main keep their ABI spelling.
- REQ-006: exercise two providers with different Cell/Leaf layouts, same-named
  default helpers, method variants, reexports, and numeric ID collisions; retain
  a runtime array push control.
- REQ-007: report actual verification limits, including native execution and
  elapsed-time/RSS evidence, without admitting the Rust seed as the runtime.
