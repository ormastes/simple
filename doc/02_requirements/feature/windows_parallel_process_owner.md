# Selected Windows parallel requirements

The user explicitly requested full80-thread builds/tests and actual blocker repairs.

- REQ-WIN-PAR-001: honor explicit80 workers; demonstrate80 simultaneously live children in two waves.
- REQ-WIN-PAR-002: retain exact native exit codes and separate bounded summary capture; quoted Unicode/metacharacter argv and private HOME/TMP/cache state must survive.
- REQ-WIN-PAR-003: stale/unknown tokens never reach legacy HANDLE operations or affect a later wave.
- REQ-WIN-PAR-004: cancel/timeout reclaim the complete owned JobObject tree; failed admission/overflow cannot pass.
- REQ-WIN-PAR-005: more than1024 historical starts remain supported without recycling identities; record real parent peak RSS.
- REQ-WIN-PAR-006: pool backpressure returns to polling and parent commits manifest-ordered results; automatic process/core limits do not silently override explicit worker requests.

Native-backend test compilation is separate issue2187. Compile-to-SMF semantics remain unchanged in this lane.