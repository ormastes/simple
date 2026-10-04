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

Structural gates: working/staged direct-env PASS; numbered-artifact guard PASS;
executable specs under doc/06_spec: 0. Whitespace found a trailing blank line in
the readiness ledger; that line was removed and the check then passed.
Committed test-tree delta PASS: 3151 inherited offenders, zero introduced;
base bcd4dd3be474a5ff17a22a328e4a35193971515e, tested head d1acf81e8f72e62b9a5bafaa511ec077e56308bf.
Offender list: C:/dev/simple/.git/item4-resource-evidence-preexisting-offenders.txt
SHA-256: 52ac058b29cffa22e435ff81da0cfb5de6db910b102fa51759866e24fd1d4678.
Later changes only document the upstream Windows facade and normalize whitespace.
The eight-commit rebase range-diff was unchanged; new upstream owned-process
functions and completion receipt remain intact. These checks do not run Simple.
Structural CI passed on 88d0f05d9e7a962f3e8f7107c8efff4cf253660e. Original
provider/classifier and seven-scenario acceptance source reviews found no P0/P1;
rebased integration preserves the upstream Windows owner additions. Runtime
qualification remains UNRUN, independently of these structural results.
