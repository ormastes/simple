<!-- codex-research -->
# Kernel/Plugin Migration Requirements

Status: FINAL. The user selected the canonical policy recorded in
`doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn` on 2026-09-02.

- **KPM-REQ-001 — Classified closure.** Every owned compiler file shall be
  classified K0, K1, or P; K0-to-P imports and unclassified files fail closed.
- **KPM-REQ-002 — Stable shared identities.** Shared contracts shall use the
  exact names `IfaceId`, `ParamHeader`, and `ParamExt`. `IfaceId` identifies
  name/major/minor/digest; parameter objects start with `ParamHeader` and end
  with `[ParamExt]` under append-only/versioned evolution rules.
- **KPM-REQ-003 — Real ABI digest.** `simple/abi-interface/v1` shall encode typed
  public ABI shape including field ordinal/name/type, change on ABI surface
  edits, ignore function-body-only edits, and remain compute-and-log until its
  gate is separately admitted.
- **KPM-REQ-004 — Fail-closed negotiation.** Static and dynamic plugin entry
  paths shall negotiate identity before returning an operational interface;
  incompatible major/digest or unknown manifest schema returns a named error.
- **KPM-REQ-005 — Param-object enforcement.** Lint/checker evidence shall reject
  reordered/removed prior fields, missing headers/extensions, silent no-op
  placeholders, and direct hot-path environment reads.
- **KPM-REQ-006 — Recorded then checked.** Artifact manifests and bootstrap
  receipts shall record provider, requirement, ABI, link mode, and negotiated
  result before those values control admission or cache reuse.
- **KPM-REQ-007 — Static seam proof.** Lint-rule and backend tables shall prove
  registration and refusal behavior without per-node indirect calls or K0
  changes for a new P-static provider.
- **KPM-REQ-008 — Narrow rebuild trigger.** A P-only edit shall not change the
  kernel bootstrap input/cache identity; a K0 edit shall change it.
- **KPM-REQ-009 — Mutation-red evidence.** Each migration phase shall include a
  positive contract and an injected defect that makes the same checker fail.
- **KPM-REQ-010 — Selected backend partition.** LLVM and Cranelift are K1 in
  the single `llvm-cranelift` composition; LLVM is the bootstrap default and
  Cranelift remains an explicit backend choice within that composition.
- **KPM-REQ-011 — Selected ABI epoch.** `SIMPLE_ABI_VERSION` is 1 now; deferred
  or compatibility-zero ABI policy shall be rejected by production admission.
- **KPM-REQ-012 — Selected manifest ownership.** `simple.sdn` is the sole
  canonical plugin manifest; `plugin.sdn` shall not be discoverable or admitted.
- **KPM-REQ-013 — Selected coverage cutover.** Coverage uses the atomic APK-only
  path. Legacy source rewriting and dual-path production execution are rejected.
- **KPM-REQ-014 — Phase 8 package-range lock resolution.** After Phase 7,
  `simple lock` shall resolve declared `provides` against caret/tilde
  `requires.range` constraints, record the selected `provides/requires`
  resolutions, and fail with an attributed lock error when no provided version
  satisfies a required range. The generated lock receipt shall also bind the
  selected `simple-sdn` manifest-location and `v1` ABI-epoch policy state;
  absent overrides shall resolve to those selected values; deprecated or
  unknown alternatives shall fail without replacing an admitted lock. Planned evidence is
  `test/01_unit/app/pkg/requires_range_spec.spl`.

A general or backtracking package-range solver and typed facets remain out of
scope. KPM-REQ-014 is the bounded Phase 8 satisfaction-and-lock contract, not a
general dependency-solving policy.
