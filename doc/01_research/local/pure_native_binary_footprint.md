<!-- codex-research -->
# Pure-native binary footprint — local research

Status: research complete; options only.  No final requirement, runtime default,
ABI, provider selection, or release admission is approved by this document.

## Scope and source state

This repair was researched against the requested fresh `origin/main` tree
`79ef60f34a5`.  The working tree may contain other agents' changes; the paths
listed below are the evidence anchors rather than a claim about a live build.

Commit `901b3fa290c` is **unselected draft evidence, not an integration
authority**.  It added feature/NFR/design/plan documents but no local research,
domain research, options, knowledge selection, executable specs, generated
manuals, source changes, audit invocation, or immutable receipt.  Its numeric
anchors therefore remain hypotheses until an owner-issued receipt binds them.

## Existing selected contract to preserve

`doc/02_requirements/feature/runtime_optional_provider_binary_size_optimization.md`
is already selected.  It requires demand-loaded, admitted providers; exact entry
closure; pure-Simple/foreign dual mode; explicit `release-small`; and receipts
that explain retained roots.  Its NFR-007 sets the sampling floor: **at least
30 samples in development and 100 in release** for size/startup gates, with
p50/p95, RSS, hashes, toolchain identity, and checksums.

The existing enforcement path agrees:

- `scripts/check/check-runtime-binary-size-startup-cohort.shs` and its producer
  select 30 for `development` and 100 for `release`, reject asymmetric samples,
  require a non-seed Stage4 receipt, check the NoGC and optional-provider
  inventories, and retain raw time/RSS samples.
- `scripts/check/check-binary-size-go-parity.shs` verifies stage4 provenance,
  stripped and unstripped artifact identity, target identity, deterministic
  source fingerprint, tool identity, and semantic equivalence.  It is useful
  evidence but is not itself a full provider/segment receipt.

Consequently the draft's proposed “at least 15 fresh processes” is incompatible
with the selected 30/100 contract.  No option below may weaken that floor;
15-sample rows can only be exploratory and are never admission evidence.

## Local findings

1. `doc/04_architecture/binary_footprint_attribution_v2.md`, its detail design,
   and `test/03_system/infrastructure/binary_footprint_attribution_v2_spec.spl`
   are the closest established evidence precedent.  They require an owner-issued
   immutable receipt bound to exact artifact digest, bytes, target, strip state,
   and authoritative reader; fixtures explicitly cannot grant admission.
2. The draft's P3 closure concept is consistent with the existing native-build
   and Stage4 boundary: one prevalidated manifest resolves requested symbols to
   unique providers before the linker runs; `native_all` must remain an explicit
   lane, never a missing-provider fallback.  The draft's historical counts and
   “two supplied audit receipts” are not independently usable because it names
   no receipt path, digest, invocation, timestamp, or audit scope.
   Today ordinary compilation instead has a coarse fixed C runtime roster, while
   Stage4 already has a requested-symbol fixed point.  The latter is not yet the
   ordinary-build authority.  The existing native-closure receipt and Binary
   Footprint Attribution v1/v2 models provide useful digest/byte primitives but
   explicitly do not grant production admission in their current forms.
3. Draft P5 receipt fields are incomplete.  `FootprintFileRowV1` has aggregate
   load bytes but no canonical input/runtime/provider/workload manifests, no
   per-load-segment kind/offset/flags, no canonical dynamic-dependency schema,
   no reader/tool version and digest, and no canonical receipt digest/signature.
   Its samples omit candidate ID/command, fresh/warm/cache label, timeout,
   failure/truncation/output-byte fields, host-load metadata, file-backed bytes,
   and private-dirty bytes.  These omissions prevent a result from satisfying
   the stated reproducibility, RSS, and bounded-execution claims.
4. Native work is intentionally not a “make everything pure” rewrite.  The
   preserved leaf boundary includes executable/file mapping, W^X, relocation and
   raw calls; OS TLS/trust-store/socket integration; GPU/device driver APIs;
   window/display/event backends; audio/browser/backend loading; and foreign ABI
   marshalling.  Pure Simple may own policy and algorithms above those leaves;
   it must not turn an unavailable native capability into a success stub.
   “One dynamic-loader owner” must be scoped to the generic runtime ABI owner:
   independently owned backend loaders (for example window or GPU leaves) are
   preserved and are not accidental duplicates.

## Research gaps that selection must close

- Name the authoritative audit commands, exact paths, input scope, producer,
  source digest, timestamp, and receipt digest before adopting any draft count.
- Decide whether the first selected packet is evidence-only, exact closure, or
  the wider ownership/provider migration.  These have materially different
  risk and file scope.
- Freeze a versioned manifest and receipt schema before setting a size target.
  It must distinguish primary artifact, provider, runtime closure, installed
  total, load segments, and dynamic dependency closure.  A pair-level admission
  receipt must bind immutable control and candidate receipts, profile/workload
  manifests, policy/evaluator digest, and per-NFR verdicts.
- Retain the existing selected 30/100 sample policy rather than carrying the
  draft's 15-sample proposal into a future requirement.

## Primary in-repository sources

- `doc/02_requirements/feature/runtime_optional_provider_binary_size_optimization.md`
- `scripts/check/check-runtime-binary-size-startup-cohort.shs`
- `scripts/check/produce-runtime-binary-size-startup-cohort.shs`
- `scripts/check/check-binary-size-go-parity.shs`
- `scripts/check/produce-binary-size-go-parity-evidence.shs`
- `doc/04_architecture/binary_footprint_attribution_v2.md`
- `doc/05_design/binary_footprint_attribution_v2.md`
- `test/03_system/infrastructure/binary_footprint_attribution_v2_spec.spl`
- `901b3fa290c` (draft evidence only)
