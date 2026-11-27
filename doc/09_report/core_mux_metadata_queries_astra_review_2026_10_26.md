# CoreMux metadata queries — independent Astra source review

Status: **SOURCE_REVIEW WARN / RUNTIME NOT_RUN / DOCGEN NOT_RUN**.
Reviewed the frozen four-file candidate described by
`build/review/coremux-metadata-source-v1.sdn`, observed base
`3006afa9b4dd286e3beb304dbe4f1a57cf5d87a8`. No remaining blocking source
defect was found. This is not a compiler, SSpec, native-provider or release PASS.
The reviewer changed only this report; author files and other lanes are untouched.

## Findings and disposition

- **P2, corrected before freeze:** Window scope initially reused its derived
  parent-session filter when selecting clients. That dropped a valid client with
  an exact window and nil optional session context. Frozen wire graph validation
  permits this context, and window-scope exchange validation requires only the
  exact window. Production `core_mux_metadata_queries.spl:93` now selects by the
  original scope. The concrete regression at
  `core_mux_metadata_queries_spec.spl:159` requires the client to survive with
  session still nil. The frozen source contains the correction.
- **Qualification limitation:** All sixteen cases are authored, with zero
  compiled/executed cases. Manual line 3 states the same. It is a source-authored
  case/expectation inventory, not generated-manual admission. SPipe generation,
  zero-stub checks, SSpec-maintain and runtime evidence remain pending under the
  root's existing execution plan. No retry or execution was attempted here.

## Reviewed boundaries

| Boundary | Source evidence and assessment |
|---|---|
| Namespace and handle | Lines 12–17 compare namespace and the complete owner/generation/lease tuple, then validate the whole input snapshot. This is correlation/shape, explicitly not authentication. |
| Scope references | Lines 36–51 validate reference owner/generation/kind and require actual snapshot membership; absent scope fails instead of producing a successful empty namespace. |
| Ancestors and visibility | Lines 52–71 retain the requested window's actual parent and filter panes only by scope, independent hidden state, and explicit Exited state. Zoom occlusion is not inferred as hidden. |
| Reference pruning | Lines 19–30 and 72–103 retain existing references only; excluded optional references become nil. Layout entries are removed without coordinate changes, reflow or replacement focus. Input validation makes ID-keyed membership maps safe for these known kinds. |
| Zoom pair | Lines 82–89 clear both zoom target and restore layout when the target is excluded; retained restore rectangles are filtered with the same pane membership. |
| Frozen representability | Lines 104–109 preserve metadata/limits/capabilities and validate the projected graph again. A required-reference/shape violation returns InvalidRequest instead of inventing a placeholder. Current DTOs permit the pruned references to be nil. |
| Current context | Lines 111–120 require an existing exact client and return its context, even when it differs from session-global focus. Only a missing self-reference is bound to that already existing client identity; no session/window/pane focus is invented. |
| Errors and side effects | Lines 8–10 return NotApplied, empty affected references, and no cleanup claim. The module has immutable inputs and no host calls, service registry, PTY drain, backend capability promotion or native-child assertion. |

Reviewed against the small-module guide, accepted caret_mux_tui requirements and
architecture, scoped snapshot design, `observation_v1.spl`,
`request_validation_v1.spl`, `wire_validation_v1.spl`, and
`wire_exchange_v1.spl`. The production file is 120 lines; no shared contract edits
are needed for this bounded implementation.

## SSpec and manual review

The sixteen `it` blocks call the production functions using the existing
`describe`/`it`/`step`/`expect` surface and built-in matchers. Setup provides DTO
fixtures; checker helpers assert concrete IDs, counts, revision, geometry, child
variants, references and typed errors. Assertions are not placeholder passes or
copies of production filtering. The fixtures explicitly do not prove native PIDs.
Coverage includes binding mismatches, malformed hidden-away input, bounds,
partial contexts, exact scopes, hidden/exited exclusions, unknown/running
preservation, zoom-pair pruning and current-context non-refocus. All sixteen
manual rows agree with those source cases and retain the NOT_RUN limitation.
No coverage percentage, runtime value semantics or generated-manual score is
inferred from this inspection.

## Exact reviewed SHA256 pins

| Artifact | SHA256 |
|---|---|
| `src/os/apps/smux/core_mux_metadata_queries.spl` | `305310e7e820011cbf15a3ac81a429bf5819188af71312b05a11829f3f42cd2d` |
| `test/01_unit/os/apps/smux/core_mux_metadata_queries_spec.spl` | `b9e1f69b1fc004762bbe8d7c7e4962b73f5210dcd89dbb0de134ad452495d366` |
| `doc/06_spec/01_unit/os/apps/smux/core_mux_metadata_queries_spec.md` | `132d819d02f0bd89dffb01d3e2118f5543890cdd4c25e687221e7fd865319b67` |
| `doc/09_report/core_mux_metadata_queries_source_2026_10_26.md` | `8eccc694a73c2ea4f0f5e20fe52858a07ff6dacc9ca4bc7f962f3a8361367264` |
| `build/review/coremux-metadata-source-v1.sdn` | `84a376a946cb9db691df283a9e26b7abd91dad5c41516150fb83c82ad2eb08ce` |

These hashes matched the frozen manifest during this review. No compiler, build,
test runner, doc generator, native helper, staging, commit or publication ran.
