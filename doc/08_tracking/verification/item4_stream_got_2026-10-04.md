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
