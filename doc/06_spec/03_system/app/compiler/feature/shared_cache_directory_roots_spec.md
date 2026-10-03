# Shared cache native directory ownership

Manual source: `test/03_system/app/compiler/feature/shared_cache_directory_roots_spec.spl`.
Status: executable SSpec **UNRUN**; this manual is maintained from its steps,
not represented as generated execution evidence. Requirements: REQ-004/007.

The native runner supplies absolute `SIMPLE_DIRECTORY_PROBE_SHARED` and
`SIMPLE_DIRECTORY_PROBE_PRIVATE` sibling roots in an isolated diagnostic tree.
Missing setup fails immediately. The candidate runtime must include the native
directory owner; a C selfcheck alone cannot qualify generated Simple calls.

1. Open runner-owned shared and private sibling roots through SOSIX. Require a
   positive generation, nonzero distinct physical identities, and successful
   revalidation. Close ownership and require stale-token rejection on both
   revalidation and a repeated close.
2. Ask the owner to admit the shared directory as private state. Require exact
   overlap rejection for both equal roots and a nested prospective private
   subtree. The C host check separately verifies no forbidden directory exists.
3. Exercise actual native path validation with relative, traversing and empty
   inputs. Every input must fail admission.

The bounded native C host suite additionally tests concurrent cold creation,
Windows SUBST/junctions/root and ancestor rename, Linux bind/mount replacement,
and a moved bind backing directory. See
`doc/03_plan/sys_test/shared_cache_directory_roots_v1_evidence.md` for actual
receipts. The full parse-cache acceptance matrix still requires bidirectional
publication/hydration, corruption/mutation isolation, and deployed bootstrap
evidence; these scenarios establish only the directory ownership boundary.
