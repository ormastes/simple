# Traceability strict SDN component TDD

STATUS: WARN — local syntax/compatibility increment, not full product verification.

The isolated product worktree is `/home/yoon/dev/simple-traceability-product-20261011`,
branch `work/traceability-product-20261011`, based on compiler prerequisite source
`39a4cfbf06564a66cb7467dfa48976a5d0946aff`. Prerequisite PR #2955 has landed on
release/1.0. The earlier scalar-only fixes are submitted separately in draft
PR #2956. The strict and typed summary changes are being consolidated with that
scalar repair for release-targeted integration; this increment has not landed.

## Observed execution

| Capsule | Actual result | Meaning |
|---|---|---|
| strict-document red2 | 8 examples, 8 failures | Actual legacy parser accepts malformed nested/whole-document input |
| strict-document green2 | 16 examples, 0 failures | First strict implementation; retained source snapshot predates Astra corrections |
| strict-roundtrip red | 3 examples, 3 failures | Independent review-derived nil/text/scientific/quoted-key regressions |
| strict-roundtrip green | 10 examples, 0 failures | Final grouped correction, including exact nested payloads, node charges, late UTF-8 location and multiline row/section ownership |

The failed first RED construction is retained: ordinary brace literals were
interpreted as interpolation. A later first GREEN construction failed on a raw
quoted-key test literal. Neither construction failure is an executed test RED.
Corrected literal syntax was used; no unsafe stub fallback was enabled.

Rust was used only for bootstrap construction from immutable pinned inputs.
The actual executed artifacts are native pure-Simple capsules: 49 modules for
the initial strict run, 50 for the final compatibility run, zero failed modules.
The retained eight- and three-case RED process exits are zero despite semantic
failures; the real SSpec summary supplies the verdict. All negative and
unexpected-variant checks assert computed outcomes through built-in matchers.

## Implementation

`std.common.sdn.strict_v1` and `strict_types_v1` add opt-in UTF-8 validation,
full consumption, located errors, nested parsing without recovery, decoded-name
uniqueness and cumulative resource limits. Existing scalar conversion and escape
owners are reused. The canonical encoder and strict decoder share float spelling
recognition; nil remains ordinary text. The base-encoding UTF-8 owner now exposes
located issues while preserving its existing text-error compatibility facade.

The exact final six-source bundle has SHA256
`f33532fecad7e3fca0a9956dc75f3bdb74d328f3b8abfa409317c46b556b917b`.
Snapshots, constructor/producer digests, logs and bootstrap input stamps remain
under `build/native_probe/`. The companion SDN diagnostic records their actual
digests and separate source stages; it is not a trusted execution receipt.

## Review and qualification limits

Astra's first source review was WARN: two P1 defects plus quoted-key lookahead,
location and positive-oracle gaps. Grouped corrections and the final ten cases
address those findings. Final Astra high-effort component source review: PASS, P0=0/P1=0, bound to
the recorded six-source bundle. Two P2 documentation clarifications are resolved
in the strict design: bare block-sequence text may contain spaces, and UTF-8
locations identify the diagnosed failure under explicit validation precedence,
without claiming earliest malformed-prefix detection for overlapping defects. No unchanged passing spec was rerun; the earlier sixteen
cases remain evidence for their preserved source snapshot only.

This does not complete AC001/AC002: the subsequent typed summary increment is
documented separately; full typed families, multitable family encoding/reference
closure and production CLI are missing. The native
fail-only defect, broad compiler/lib/MCP/LSP checks, generated-manual review,
branch coverage, runtime/NFR qualification and protected admission remain open.
All 20 REQ-TRC / 40 AC-TRC / WP0–WP7 obligations are retained.
