# Typed selected export provenance

Status: authored, execution UNRUN. Source owner:
`test/01_unit/compiler/hir/module_surface_selected_exports_v1_spec.spl`.

The fixture parses real source, builds module surfaces, freezes configured routes,
and calls the typed selection and hop APIs. It checks:

1. Public declaration versus explicit facade export and direct terminal marker.
2. A named alias with legacy export target -1 binds through its configured import;
   changing that target causes the retained hop read to fail.
3. Both same-terminal named routes retain intermediate exported bindings.
4. Distinct terminals in a winning tier are ambiguous and uncacheable.
5. An unavailable named tier cannot fall through to a resolved glob.
6. Function/type collisions remain typed; legacy name-only lookup is unavailable.
7. Explicit private cannot be promoted; cycles cannot invent terminals.
8. Out-of-range hops, corrupt windows and stale generations fail closed.
9. Stable identity excludes allocation generation but includes changed intermediate routes.
10. Selected-only folder membership does not establish complete sibling lookup.

The pre-existing same-folder plain-export fixture remains an additional open
compatibility requirement until actual sibling-selection authority is integrated.
No runtime, compiler, or protocol qualification is claimed by this manual.
