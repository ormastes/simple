# Native history acceptance plan

REQ-SCV-HISTORY-001: integration diamond assertions plus the system scenario's
real conflicting merge prove both parents, deterministic DFS, and deduplication.
The lifecycle scenario checks legacy default log compatibility.

REQ-SCV-HISTORY-002: system snapshot/open/close/new-change assertions capture
exact stable IDs and revision counts. Integration v1 and independent-root
fixtures prove selection starts from the change record's latest. Mismatched
latest identity must fail.

REQ-SCV-HISTORY-003: integration negative assertions cover cycle, unavailable
second parent, malformed/unsafe metadata, nonregular reads, and separate node,
edge, and byte limits. System scenarios require nonzero CLI exits and no
partial history on failure.

Run each acceptance command once with an admitted pure-Simple runtime. No such
runtime is present in this worktree; execution, coverage, manual generation,
and maintenance scores are NOT_RUN. Static shell syntax and facade checks are
supplemental evidence only.
