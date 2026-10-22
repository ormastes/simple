# Generic nominal specialization identity

Scope: H-NAMED from the generic instantiation model, continuing the user's
request for complete generic implementation and robust release bootstrap.

REQ-GENERIC-NOMINAL-IDENTITY:

- Distinct declarations with the same short name have different specialization
  keys, including nominal leaves nested inside containers and function types.
- Imports of one declaration share a key despite different module-local ids.
- The canonical owner and declared type name have unambiguous component
  boundaries. Display mangling remains separate and retains collision suffixes.
- A missing owner, missing symbol table, or value symbol used as a nominal type
  cannot admit a specialization. Two unknown identities do not compare equal.
- Production inference checks nominal declaration ownership even for a fixed
  nominal parameter. Cross-module inference never falls back to raw-id equality
  when the ownership context is unavailable.

Evidence: `generic_specialization_owner_key_spec.spl`, owner-binding specs,
and the updated production/model differential setup. The native fixture under
`test/fixtures/bootstrap/generic_owner_identity/` requires two emitted LLVM
identity definitions, followed by execution matching `main.expected`.

These criteria concern nominal specialization identity. Caller/provider HIR id
relocation, cross-module return ABI, and generic function-template name
collisions are separate obligations and must not be inferred from key tests.
