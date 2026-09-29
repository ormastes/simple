# System-test plan: Simple cross-language performance acceptance v1

## Scope

The canonical executable is
`test/05_perf/simple_cross_language_perf_acceptance_v1_spec.spl`; its mirrored
manual is
`doc/06_spec/05_perf/simple_cross_language_perf_acceptance_v1_spec.md`.
This matrix covers startup, interpreter execution/memory, compilation,
generated-binary footprint, dynlib/aspect loading, and cache behavior.

## Frozen matrix

| ID | Success | Boundary | Refusal | Evidence owner |
|---|---|---|---|---|
| SLP-A01 | Minimal startup capsule closure plus paired startup receipt | `.spl`/`.shs` route and mmap/read fallback | Unknown policy/non-source route | startup selector and admitted startup collector |
| SLP-A02 | Interpreter semantic oracle plus paired wall/RSS/allocation receipt | Unpaired-surrogate replacement | Missing allocation-count evidence | interpreter/runtime receipt owner |
| SLP-A03 | Frozen compile fixture/checksum plus compile receipt | Changed oracle checksum | Changed argv/no fallback | L10 output protocol and compile collector |
| SLP-A04 | Native generated-binary closure receipt | Manifest invalidation | Missing/static-only manifest | binary closure owner |
| SLP-A05 | Authenticated typed dynlib/aspect query receipt | Missing-symbol typed error | Unauthenticated provider artifact | dynlib/provider loader owner |
| SLP-A06 | Resolver repeated-miss reuse | Caller-sensitive reset generation | Stale effect plan after source change | module resolver/cache owner |

Every group has one success, boundary, and refusal scenario with critical
importance weight 3.  Model and host-contract assertions may pass independently;
physical performance claims remain `MissingEvidence` until the production
owner supplies an immutable receipt.  No timing threshold, RSS number, or
language ranking is synthesized here.

## Verification

Run the executable spec once on the admitted self-hosted binary, then generate
the mirrored manual with `spipe-docgen ... --output doc/06_spec --no-index`.
Review that all 18 scenarios retain stable IDs, real assertions, the weighted
metadata suffix, and explicit unavailable/refusal reasons.  Do not place an
executable `.spl` spec under `doc/06_spec`.
