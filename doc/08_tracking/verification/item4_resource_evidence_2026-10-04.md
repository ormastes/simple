# Resource evidence prerequisite verification

STATUS: FAIL — full item4/Phase 4 remains incomplete.

The linker measurement classifier previously promoted ExactTree plus a caller
limit to QualifiedJobScope without enforcement authority. Test intent precedes
its repair: valid observations remain MeasuredOnly, invalid/absent observations
NotCertified, and this API never sets certified_under_limit.

The actual cgroup observer must require valid current and peak counters instead
of fabricating a zero for missing memory.peak. The actual systemd caller uses a
strict successful/nontruncated metric parser. Its numeric range follows the
existing portable 2^60-1 converter ceiling. Five resource scenarios use real
metric files and production parser paths; two classifier scenarios test the
classification boundary. They do not simulate or certify kernel enforcement.

Current hosted defaults already select external linkers; process, user and
machine SIMPLE_LINKER overrides were all unset. Explicit SIMPLE_LINKER=internal
remains accessible and is documented without changing routing or SimpleOS policy.

Compiler/lib/MCP checks, native execution, SSpec/docgen, branch coverage and NFR
remain UNRUN because there is no admitted self-hosted runtime in this lane.
No capped runtime build was retried. Full before-exec/no-swap/descendant worker
admission and parent-owned publication remain implementation obligations; existing
UnsupportedBudget and provider qualification refusal are preserved.
