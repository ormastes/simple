# Optimization and target-profile coupling

Observed on release `a132155869c`: positive MIR optimization silently sets
`release=true`; standalone/native CLI paths repeat that inference. Managed
Phase 3 and Phase 4 authorities both select release, while command manifests
omit an explicit target profile. Their old normalized variant fields do not
bind requested debug policy or resolved observer availability.

The repair separates optimization from target profile, canonicalizes legacy
release/profile/build-mode fields, and retains authoritative native-build
release defaults. Explicit development stays development at any optimization
level; explicit release can use level zero. Conflicting explicit CLI profile
requests are rejected in either order. `--managed-build-phase` selects target
policy, never producer identity or admission authority.

The shared typed result carries build profile, requested debug policy, and
Disabled/Unavailable/Available observer resolution. Static XRay emission stays
separate from observer activation. Ordinary defaults remain unchanged; managed
Phase 3 requests development debug automatically. Missing actual observer
admission yields a stable unavailable reason, not Available or active recording.
Present observer extensions map Off to Disabled and Dynamic to Enabled; malformed, conflicting, and AlwaysOn requests fail before cache lookup. Explicit unavailable observer requests fail. Release rejects explicit XRay or
observer enablement and resolves automatic debug to Disabled.

Compile caches frame profile identity separately from optimization and static
XRay. The new schema invalidates old keys; the no-op cache re-resolves policy
and binds the managed phase. Native object namespaces and module witnesses bind the resolved policy plus independent static XRay and actual output format. Managed index/authority/readback and resume inputs
must use the same normalization and reject old option sets. Producer identity
remains separate. Source, ABI, and toolchain admission are unchanged.

## Evidence and limits

Native producer SHA-256:
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
Every probe used one thread, core-c, private object/XDG caches, sampled 2 GiB
process-group RSS bound and 120-second deadline; no address-space limit.

- Actual 14-record CompileOptions/dependency projection: native PASS, 7.480 s,
  78,938,112-byte sampled peak RSS. Original normalization functions from the
  baseline compiled successfully, then the same assertion exited 1 because
  optimized development became release.
- Actual compile-options hash and actual SHA-256 byte implementation: PASS,
  10.852 s. Profile, optimization, and old-key identities differ. Framed
  adversarial reason text cannot alias another policy. Production positional
  call shape was exercised.
- Actual no-op normalization plus actual managed/SHA implementation: PASS,
  10.405 s. Ordinary, managed, and explicit-disabled identities differ; invalid
  release/XRay cannot produce a reusable identity. Its initial fixture extractor
  truncated a multiline declaration; that parse failure is retained.
- Actual TraceConfig/defaults and observer-result policy boundary: six distinct presence/error cases PASS, 6.816 s. The existing SDN parser integration itself remains UNRUN.
- Actual native object policy identity and SHA implementation: PASS, 9.975 s; profile, static XRay, and Native/Both packaging separate keys; missing identity is refused. Full object-cache execution remains UNRUN.
- Managed lane adds 30 native profile/receipt cases, two focused debug-info-default cases, and bound command-option checks.

[Retained commands, exits, logs, provenance, and extraction scripts](evidence/target_profile_2026_11_14/).
Core fixture regeneration: `python3 scripts/check/target-profile-projection.py
<fresh-private-output-directory>`. The archived launch scripts describe their
original local layout; they are evidence, not a bootstrap entrypoint.

Full-import SSpec, full CLI dispatch, core/MCP smoke, manager resume, and Phase
3/4 bootstrap qualification are **UNRUN**. This is bounded source-policy
verification, not feature completion or runtime tracing admission.

A separate old-producer defect was exposed: a named seventeenth argument after
omitted default arguments is silently dropped. The nine-line text reproducer
and failing native exits are retained; the separate bug
`named_default_tail_argument_misbind_2026_11_14` owns that repair.
The positional production call was already the real call shape. This profile
repair does not claim to repair the compiler's named-argument lowering.

The PR source-binding gate detected the new target-profile hash component missing from the formal live-key schema. The correction adds component50, regenerates its Lean visibility theorem through the actual native schema parser/emitter, and re-pins only the reviewed hash declaration. The compiler-free source-binding check passes41 bindings. Lean compilation and full generator execution remain UNRUN on this host; this does not expand the scoped verification claim.
