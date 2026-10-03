# Source and test artifact binding: domain evidence

Date: 2026-10-03. Scope: REQ-019 admission and the remaining source/test mapping
gap, under the already selected requirements. This adds implementation research;
it does not select a new feature option or declare runtime acceptance.

## Primary evidence

- [SLSA provenance](https://slsa.dev/spec/v1.2/provenance) describes build
  provenance as tracing outputs back to the source used to produce them.
  The [upstream build-provenance specification](https://github.com/slsa-framework/slsa/blob/main/spec/build-provenance.md)
  recommends reading configuration from version control and recording verified
  source identity and resolved dependency digests. A producer-supplied label is
  not equivalent to an observed, digest-bound input.
- [Reproducible Builds' definition](https://reproducible-builds.org/docs/definition/)
  requires identical specified artifacts to be recreatable from the same source,
  environment and instructions. Its [environment discussion](https://reproducible-builds.org/docs/perimeter/)
  makes the declared build environment part of that claim.

These primary pages were located through web search on the date above. They
support the narrow concepts stated here, not a claim that this implementation
conforms to SLSA or has demonstrated reproducible execution.

## Consequences for the selected local design

The following are design inferences, not quotations or external requirements:

1. Keep immutable semantic revision identity distinct from the digest of its
   stored artifact envelope. Record and validate an explicit binding; slicing
   `sha256:v1:` off a semantic revision does not create a CAS locator.
2. Preserve existing signed records and exact accepted replay. Strengthening
   new admission needs an explicit versioned representation and compatibility
   rule, rather than reinterpreting previously signed fields.
3. Source/test mapping metadata must be exact and reachable through captured
   state. Artifact availability is independently observed and may honestly be
   missing, restricted or expired; such observations do not establish present
   reproducibility.
4. Verifying an opaque artifact and its signed mapping proves only that binding.
   Source-tree completeness, path/mode semantics, executable instructions,
   toolchain/environment capture and a successful reproduction require their
   own defined formats and evidence. No imported reproduction executes during
   admission.
5. Test substitution, changed source mapping, unregistered revisions, wrong
   digest domains, stale captured state and lost dependencies must have real
   filesystem/owner regression cases. Test-source existence is not executed
   RED/GREEN evidence.

The implementation proposal and compatibility decisions are recorded separately
in the focused local research/design artifacts. Full REQ-019 and Operating B
remain unqualified until their complete acceptance evidence exists.
