# Selected-child requester regressions

Status: fourteen authored executable cases; UNRUN. RED/GREEN execution is blocked by
the absence of an admitted general pure-Simple SSpec runner. The frozen policy
fixtures are injected test inputs, not evidence of driver/frontend authentication.

Executable: `test/01_unit/compiler/hir/module_child_requester_v1_spec.spl`.

| Actual HIR path | Expected behavior |
|---|---|
| Named type through public/private aliases sharing a target | Public succeeds; private reports `private-child` |
| Named export facade versus selected private implementation route | Facade succeeds; direct route is denied |
| Folder-local declaration exported explicitly | Facade promotes it; direct outside-folder access is denied |
| Same-ID rebind or changed policy | Stale provenance is denied |
| Sibling access to omitted versus `pri` declaration | Omitted remains folder-local; `pri` remains file-private |
| Public child under another closed ancestor | Ancestor remains closed |
| Namespace and containing-type expression | Rejected before public member resolution can bypass it |
| Local alias declaration elaboration | Imported private route remains checked |
| Legacy flat import without selected-child provenance | Existing behavior remains unchanged |

The suite exercises production parser, registry freeze, import binding writes and
actual named-type/expression lowering. It does not prove runtime execution,
qualified/glob-export authorization, cross-directory facade chains, all implicit
qualified-name fallbacks, or complete member/type access enforcement.

Safety review added two negative closure cases. Three further positive cases
retain the required success expectation and are KNOWN UNSUPPORTED on this source:
valid imported public aliases, valid generic defaults, and sibling facade export
without a selected public implementation-child receipt. A future run is expected
to expose these gaps; this suite is not currently claimed green or complete.
