# Streamed ELF COMDAT verification

STATUS: FAIL — full item4 and Phase 4 remain incomplete.

This slice implements existing ITEM4-REQ-003/004/009 obligations for section-group
selection in the retained x64 ELF stream. Test intent f675871ad09 preceded
production edits. Acceptance inspects actual grouped objects and linked bytes;
the fast resident ELF path is not a COMDAT oracle. GNU experiments distinguish
archive symbol-record demand from errors on surviving relocation references.

Root source review corrected the first test's invalid read_window=1 setup:
name_bytes=64 and emit_window=8 violate existing admission under that setting.
The fixed test retains read/name limits and uses emit_window=1. This was an
authored-test defect, not an executed Simple failure. Production admission is
not weakened to accommodate it.

Runtime reinspection found a completed phase2 Cranelift diagnostic with exit 0,
but its result and supervisor receipts explicitly report admitted:false. The
producer is a bootstrap seed with a recorded qualification limitation, not a
deployed admitted self-hosted runner. No capped build is restarted. Exact paths
and observations are recorded in the COMDAT design document.

Simple compilation/specs/docgen, coverage, compiler/lib/MCP/native execution and
NFR evidence remain UNRUN. Constant auxiliary group state, scan quotas and bounded
payload reads do not establish whole-job memory enforcement or latency targets.
No tag or publication is authorized by this source slice.

Independent draft review corrected empty-group winner suppression and identified
missing effective-undefined semantics for discarded weak definitions. GNU probes
confirm kept local references are accepted and discarded weak references produce
zero; the implementation preserves the former and adds a regression for the
latter. Final source and acceptance reviews bind exact commits before landing.
Existing bounded-input tests still require live unresolved references to fail
inside input opening; validation is not deferred solely to image emission.

Final exact source review: core 8c926ceee33 and acceptance through 7572f1720ca
have no remaining P0/P1 findings. Thirteen authored scenarios and the manual
cover the agreed behavior; execution remains UNRUN. Working/staged direct-env,
whitespace and numbered-artifact guards passed; doc/06_spec executable count 0.
The eleven-commit rebase onto 3f1191dd28351da8aa4a91119fd3210d91f976ec was unchanged.
Structural CI passed on source head d7e5b5758471a4ddfd7cf809ab97ef3cd6572e0b.
Test-tree delta PASS: 3151 inherited offenders, zero introduced by this range.
Offender list: C:/dev/simple/.git/item4-stream-comdat-preexisting-offenders.txt
SHA-256: 52ac058b29cffa22e435ff81da0cfb5de6db910b102fa51759866e24fd1d4678.
These structural/source results do not establish runtime or Phase 4 PASS.
