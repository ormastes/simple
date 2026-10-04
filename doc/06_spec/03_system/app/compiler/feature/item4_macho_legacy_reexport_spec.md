# Legacy Mach-O reexport acceptance

Eight authored ITEM4-REQ-006 scenarios live in
`test/03_system/app/compiler/feature/item4_macho_legacy_reexport_spec.spl`.
**Simple execution UNRUN**. This companion is authored documentation, not a
generated test receipt. Independent LLVM fixture observations are recorded in
`test/fixtures/linker/macho/RECIPE.md`.

| Scenario | Concrete assertion |
|---|---|
| Inactive child deployment | A genuine symbol-table-fallback classic root supplies its own exports while an unmatched child's independently encoded macOS99 deployment remains inactive. The native image still has root ordinal1 and the expected local pointer. |
| Command validation | Real library/umbrella commands reject an out-of-command offset, header offset, empty name and missing terminator, including missing terminator with MH_NO_REEXPORTED_DYLIBS set. |
| Exact stem matching | A real dependency with an underscore suffix matches `liblegacy`; shorter `liblega` and longer `liblegacyX` do not. Version-dot matching is exercised by the main positive fixture. |
| Dormant direct API metadata | A validated real export provider with no dependencies continues to link through the typed no-closure API when inference provenance is present. Flag-suppressed selectors also preserve exact baseline image bytes. |
| Hidden dependencies | Both CPU ordinary and header-suppressed selector providers leave imports unresolved and preserve an existing destination sentinel. |
| Classic parent inference | Both CPU classic roots infer a child's `OldRoot` umbrella only from the physical parent basename. Different child name, different physical parent and a modern compressed root remain hidden. The install name deliberately differs from `OldRoot`. |
| Explicit selectors | Both CPU LC_SUB_LIBRARY/LC_SUB_UMBRELLA providers preserve original LC_LOAD_DYLIB metadata and expose the selected dependency through actual native graph linking. The resulting image has the expected root command, binding ordinal and pointer. |
| Closure requirement | Both raw and typed hosted APIs that do not construct a graph reject active legacy selectors with a named legacy diagnostic. |

The matching profile uses exact library stem before the first dot or underscore,
and exact umbrella final component for paths containing a slash. This is the
frozen project contract; no universal historical ld64 prefix-equivalence claim
is made. Explicit selectors may operate on compressed providers. Classic
inference additionally requires absence of modern export commands and the
header suppression flag. Raw dependency command identities remain unchanged.

The broader design also requires all matching dependencies, weak/lazy/upward
class boundaries, unmatched selectors with physically missing dependencies,
and additional alias interactions. Those boundaries are **not covered by this
eight-scenario wave** and remain explicit acceptance obligations. This does not
claim complete SDK or native Darwin qualification, signing validity, runtime
loading, immutable file identity or process memory enforcement.

Pending execution requires an admitted self-hosted runtime:

```
<admitted-runtime> test test/03_system/app/compiler/feature/item4_macho_legacy_reexport_spec.spl --mode=interpreter
```

No Rust seed, bootstrap rebuild, runtime retry or executed RED/GREEN claim was
used for this acceptance work.
