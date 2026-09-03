# macOS Bootstrap Reverse-Reference Native Evidence — 2026-09-03

## Verdict

**PARTIAL NATIVE EVIDENCE / PROVENANCE BLOCKED.** The available pure-Simple
release executable starts natively on Apple Silicon and satisfies the measured
startup/RSS envelope. The reverse-reference owner mutation gate rejects all 14
weakenings. Stage2, Stage3, Stage4, M4, Intel, universal, and release promotion
remain unqualified because no admitted producer-chain receipts accompany the
available executable.

This run used a clean fork at commit
`67532532552dabb24208b6687e2c23b9ae6947a9`. Only evidence and two narrowly
scoped macOS reverse-reference checker files were changed afterward. No Rust
seed fallback was used.

## Host and binary

| Fact | Evidence |
|---|---|
| Host | Darwin arm64, macOS 26.5 |
| Kernel | Darwin 25.5.0, `RELEASE_ARM64_T8132` |
| Runtime | `/Users/ormastes/simple/bin/release/macos-arm64/simple` |
| SHA-256 | `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767` |
| Mach-O | thin arm64 |
| Load command | `LC_BUILD_VERSION`, minimum macOS 26.0, SDK 26.2 |
| Signing | embedded ad-hoc linker signature; no distribution identity |
| Runtime identity | pure-Simple release command surface; the same immutable binary reported repository-derived version text (`v1.0.0-rc.1` initially and `v0.9.5` later), so version text alone is not accepted as provenance |
| Intel slice | unavailable |

Raw evidence is retained under
`build/review/macos-native-evidence-20260903/` and bound by `SHA256SUMS`.

## Startup and RSS

One cold invocation and one batch of 20 warm invocations were measured with
`/usr/bin/time -l -p`.

| Measurement | Result |
|---|---:|
| Cold wall time | 0.06 s |
| Cold maximum RSS | 10,764,288 bytes |
| Warm 20 wall time | 0.72 s |
| Warm average wall time | 0.036 s/request |
| Warm maximum RSS | 10,813,440 bytes |
| RSS delta | 49,152 bytes (0.46%) |

The observed RSS is within the selected 110% steady and 10% growth thresholds.
This is startup-process evidence only; it does not replace the required admitted
long-lived M4 server baseline receipt.

## Acceptance results

| Gate | Result | Exact evidence |
|---|---|---|
| macOS bootstrap receipt native gate | **SETUP BLOCKED** (`2`) | The sparse evidence fork omitted `scripts/release/macos-universal-m5.shs`; command was not rerun because this campaign permits each acceptance command once. |
| Stage3 static retry readiness | **REFUSED** (`1`) | `reason=diagnostic-transport-disclosure-missing`; the narrow sparse fork omitted supporting disclosure artifacts. |
| Stage3 planner admission | **REFUSED** (`64`) | `parent-compiler-not-under-build-bootstrap-stage2`; the standalone release binary is not an admitted Stage2 artifact. |
| Stage3 aggregate receiver native | **REFUSED** (`2`) | `SIMPLE_ADMITTED_COMPILER_SHA256_required`; no Stage2/Stage3 admission chain exists. |
| Stage4 runtime ABI/provenance | **REFUSED** (`2`) | No adjacent Stage4 provenance receipt exists. The checker also calls undefined `stage4_verify_source_provenance`; the canonical helper exports `stage4_verify_candidate_provenance`. This is reported but not fixed because the lane permits only `scripts/check/macos-*` changes. |
| M4 arm64 native qualification | **BLOCKED** (`3`) | `Phase3 admission receipt unavailable`. |
| Reverse-reference owner structure | **PASS** | New missing checker validates all production publication seams. |
| Reverse-reference owner mutation matrix | **PASS** | 14/14 owner/family publication weakenings rejected. |
| Reverse-reference projection SPipe | **FAIL** (`1`) | Self-hosted runner discovers the real spec but its deployed parser rejects current syntax: `expected '(', '{', or '[', found RParen`; no false PASS is claimed. |
| x86_64 native qualification | **BLOCKED** | No native Intel release candidate or admitted receipts are present on this arm64 host. |
| universal/sign/notarize/promote | **BLOCKED** | Requires both admitted M4 slices and Apple distribution signing/notary authority; only an ad-hoc arm64 binary exists. |

## Checker repair

`scripts/check/check-macos-reverse-reference-owner-publication.shs` was missing
although its mutation harness invoked it. The added checker:

- verifies every direct, module/SCC, trait, unresolved-method, annotation,
  generic, AOP, runtime-provider, initializer, and relocation publication seam;
- rejects seed identities;
- requires a non-vacuous `Results:` line from the executable SPipe spec;
- supports structural-only mutation execution so native acceptance is not run
  repeatedly.

The mutation harness now selects structural-only mode for its 14 isolated
mutations. The native spec was invoked exactly once.

## Required next native run

The next run must begin with a producer-created Stage2 artifact and its sanity,
provenance, runtime-snapshot, and planner receipts. It must not copy this
standalone release binary into the Stage2 path or synthesize receipts. After an
admitted Stage2 exists, run the documented Stage3 receipt creation, validation,
Stage2 refresh, final readiness, and Stage3 production commands once each.
Only then may M4, long-lived residency, Intel, and M5 universal qualification
run.
