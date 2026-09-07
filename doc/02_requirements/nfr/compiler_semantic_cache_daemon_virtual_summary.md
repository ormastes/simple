<!-- codex-requirements -->

# Compiler semantic cache manager NFR requirements

- **NFR-CSM-001 Correctness:** zero false hits across differential, mutation, fuzz, corruption, crash and concurrency corpora.
- **NFR-CSM-002 Fallback:** daemon failure shall add at most 250 ms before direct compilation begins; fallback shall preserve artifact and diagnostic identity.
- **NFR-CSM-003 Lookup:** admitted local action lookup p95 shall be at most 10 ms on the standard bootstrap host.
- **NFR-CSM-004 Lifecycle:** daemon idle RSS shall be at most 100 MiB and shutdown shall occur 10–12 seconds after the final request/lease/transaction.
- **NFR-CSM-005 Overhead:** cache hashing, journal and receipt overhead shall be at most 5% of warm build wall time and 128 MiB additional peak RSS.
- **NFR-CSM-006 Startup:** retained evidence shall separately cover `--help`, cache-hit query, frontend check, interpreted run, SMF load, native compile and native link, with forbidden/required capsule receipts.
- **NFR-CSM-007 Regression sampling:** each cold, unchanged-warm, private-edit, public-edit, trait/AOP-edit and link lane shall run one warmup and at least seven alternating baseline/candidate pairs on an admitted quiet-runner profile.
- **NFR-CSM-008 Regression verdict:** compute median and 20%-trimmed mean over per-pair candidate/baseline ratios. With CV at most 5%, `FAIL` when both exceed 1.10 and `PASS` when both are at most 1.10. Emit `INCONCLUSIVE` when estimators disagree across 1.10, CV exceeds 5%, or admitted-runner/evidence requirements are incomplete; allow one bounded quiet-runner retry and block release if the retry remains inconclusive.
- **NFR-CSM-009 Provenance:** every performance row shall bind source snapshot, compiler/runtime, provider, cache schema/root, target, command, hardware and baseline digests, plus wall, CPU, RSS, hit/miss/reparse counts and output identity.
- **NFR-CSM-010 Resource bounds:** decoders, MCP pages, daemon requests, journal replay and GC work shall enforce explicit byte/count/depth/time limits before allocation or execution.
- **NFR-CSM-011 Portability:** daemonless and daemon modes shall work on supported hosts, including Windows path/root semantics; platform differences remain behind existing host/runtime facades, never application forks. The configured root shall reside on one filesystem and use private per-user permissions or the Windows user ACL equivalent.
- **NFR-CSM-012 Bootstrap:** final evidence shall use admitted pure-Simple Phase 2 and Phase 3 runtimes, including compiler/interpreter/loader, CLI/tools, MCP/LSP and cache/fallback parity.
