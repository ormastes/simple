# RTI frontend core alias ownership

Authored manual for `test/01_unit/compiler/hir/rti_core_owner_alias_spec.spl`;
not generated documentation. Native execution and documentation generation pending.

Requirement: loader aliases for one physical provider share declaration ownership;
different providers must continue to fail mixed registration.

1. Parse two typed functions under `src/compiler/10.frontend/core/types.spl`.
2. Give one symbol the loader's `compiler.core.types` import spelling.
3. Generate RTI rows; require canonical frontend owner for both and two registrations.
4. Repeat with `compiler.frontend.core.other`; require E-RTI-006.

Seed diagnostics executed both cases: red1pass/1fail, green2pass/0fail.
See the linked tracking record for logs and native validation limits:
[owner alias bug](../../../../08_tracking/bug/rti_frontend_core_alias_owner_2026_10_30.md).
