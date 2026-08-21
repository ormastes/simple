# Unresolved symbol aliases fail closed

Mirror of `test/01_unit/compiler/backend/unresolved_symbol_alias_fails_closed_spec.spl`.

The executable SSpec verifies every `unknown_N` symbol aliases only to the fail-closed trap and that the trap itself is defined so linking can resolve it.

The test inspects linker/source contracts; it does not deliberately execute the trap in a produced binary.
