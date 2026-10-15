# Coverage-aware retained parser ownership

Scope: the authorized correction for the MC/DC qualification build that
exceeded 8 GiB during source parsing. Preserve coverage, MC/DC and complete
source membership; do not substitute cache hits or fabricated objects.

- **REQ-PARSE-OWNER-001:** Selected AOT parsing reclaims each source's flat-AST
  and traversal scratch before returning, including coverage, MC/DC and
  full-inventory selection. Retained parser modules remain readable.
- **REQ-PARSE-OWNER-002:** Reclamation preserves decision/condition rows,
  MC/DC obligations and contexts, collision maps, desugared functions and
  target receipts. Same-source replay preserves existing semantics: coverage
  and condition obligations deduplicate, while formal context rows append.
- **REQ-PARSE-OWNER-003:** Missing source authority remains an error, malformed
  source diagnostics remain readable after teardown, and a subsequent valid
  source parses successfully with no active scope left behind.

Executable traceability: [system spec](../../../test/03_system/compiler/coverage_retained_parse_owner_spec.spl)
and [test plan](../../03_plan/sys_test/coverage_retained_parse_owner.md).
