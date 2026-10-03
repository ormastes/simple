# Collection function declaration identity

Authored companion to
`test/01_unit/compiler/interface_compat/collection_function_identity_spec.spl`;
not generated runtime evidence. Four scenarios use the real frontend and HIR
lowering, then the canonical ABI encoder:

- Body-only changes preserve signature identity.
- Parameter type changes change identity.
- Async declaration semantics change identity.
- An unresolved named return type is rejected.

The digest covers typed declaration shape, effects and calling attributes.
It does not prove body semantics, module ownership or backend availability;
the registry caller must independently establish those facts. Tests remain
unexecuted pending an admitted self-hosted runner.
