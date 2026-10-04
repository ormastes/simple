# Streamed ordinary x64 GOT verification

STATUS: FAIL — full item4 and Phase 4 remain incomplete.

Scope is actual synthesized GOT entries and checked ordinary static x64 GOT
relocation families through the file-backed linker. Selected entry identities
must distinguish global names from local object/table/symbol identities. Addends
belong to relocation formulas, not slot identity or payload. Bounded scans and
windowed output must preserve common storage, cancellation and existing quotas.

Real test intent precedes implementation. An external GNU toolchain oracle is
research evidence only. Simple compilation/tests/docgen, coverage, core/lib/MCP
checks, native execution and NFR evidence remain UNRUN. Whole-job enforcement
remains unadmitted, and the prior capped runtime build attempts are not repeated.

Core source is now authored for all twelve ordinary types: 3,9,25–31,41–43.
It preserves first-reference order with tagged global/local identities, appends
checked slots after COMMON, and emits each eight-byte payload through bounded
windows. The original instruction encoding remains intact. Synthetic-anchor
resolution depends only on regular/COMMON storage, avoiding payload recursion.
Inactive GOT preserves the prior extent; active zero-slot GOT adds no entry.

Independent exact-commit review found one archive-loop indentation defect in the
draft; it was corrected before integration. Final core review found no P0/P1.
Additional table/record scans consume the shared quota, but their runtime cost
and whole-job memory behavior are not measured. Real test intent preceded the
source implementation; no observed RED/GREEN result is claimed.

The authored positive acceptance uses actual objects containing all twelve
relocation types, independently inspected during fixture construction. Its
program-header oracles reconstruct slot and target addresses, distinguish
equal-address global aliases from separate local definitions, and check weak
zero/common/archive payloads. Emission windows of 1, 3, 8 and 64 bytes exercise
split relocations and slots. Separate exact-size fixtures cover unused GOT
declarations and active zero-slot/scalar-anchor layouts.

Positive-test review corrected signed GOT32/64 offset decoding for the fast
linker's placement of slots before its GOT base. This was a test-oracle defect,
not evidence of an executed Simple failure. The final negative matrix and
authored manual are reviewed separately before source landing.

Final acceptance source review covers six scenarios, including malformed symbol
indices, patch bounds, signed displacement overflow, TLS refusal, reserved-anchor
conflicts, exact GOT output budgets, scan exhaustion and cancellation. Negative
cases preserve a pre-existing output sentinel. Independent review of commits
304c0f4e0cf and 38f18319261 found no remaining P0/P1. Runtime results remain UNRUN.
Working and staged direct-env guards passed; executable specs under doc/06_spec: 0.
