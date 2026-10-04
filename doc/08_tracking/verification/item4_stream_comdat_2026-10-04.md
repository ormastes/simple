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
