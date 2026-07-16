<!-- codex-design -->
# Pure-Simple tool and infrastructure hardening detail design

## Interfaces retained or added

- Reuse the existing candidate admission helper for provenance.
- Derive CLI counts from `get_command_table()`.
- Add one pure test outcome classifier returning a stable class/code pair from
  aggregate result state; keep `TestFileResult` as the file-level model.
- Use one daemon-child environment marker owned by the test-runner/daemon
  boundary. The client routes marked nested invocations to the existing
  `--no-session-daemon` path.
- Replace duplicate discovery shell calls with `dir_walk_native` and `file_read`.
- Replace CLI lint substring parsing with `Linter.lint_source`.
- Make `cli_lint_commands` the behavior owner; `lint_entry` only parses/help and
  calls it without raw-source recursion.
- Generated launcher templates own native candidate order and defaults; checked
  launchers are regenerated outputs.

## Qualification scenario vocabulary

Manual step text is frozen for sidecar and implementation consistency:

1. `Admit a pure-Simple production runtime`
2. `Run truth-preserving developer tools`
3. `Reject unsafe paths and stale fallbacks`
4. `Measure warm tooling budgets`

System-test helper names use the `qualification_*` prefix:

- `qualification_runtime_identity`
- `qualification_run_command`
- `qualification_exit_class`
- `qualification_hostile_path_probe`
- `qualification_measure_warm`
- `qualification_assert_wrapper_route`
- `qualification_daemon_cache_probe`
- `qualification_termination_probe`

Helpers must return concrete evidence or fail; no silent placeholder body is
allowed.

## Acceptance mapping

| Requirements | Main evidence |
|---|---|
| REQ-001..002 | seed rejection, atomic swap/rollback contract and post-swap probes |
| REQ-003..006 | red/empty/nonzero/sibling/nested/timeout runner fixtures and outcome classes |
| REQ-007..008 | hostile-path sentinel tests and one measured canonical benchmark |
| REQ-009..010 | multi-name scoped lint suppression and single-handler source contract |
| REQ-011 | table-derived command counts |
| REQ-012 | Unix/Windows native-first wrapper contracts and correlated MCP/LSP calls |
| REQ-013 | daemon lifecycle plus cache hit/miss/invalidation equivalence |
| REQ-014 | checker/global-flag and `gen-lean` deadline/no-recursion fixtures |
| REQ-015 | mirrored executable spec/manual and guide links |

## Error handling

- Provenance, protocol, and artifact failures are explicit nonzero results.
- Test child process failure dominates parsed summaries.
- Empty discovery is distinct from an explicitly filtered zero-result run.
- Unsupported platform evidence is recorded as unavailable and cannot satisfy
  Windows/Linux parity.

## Performance design

- Warm measurements run once after an unmeasured warm-up and then a bounded
  sample set; retain p95 and max RSS.
- Duplicate-check removal of `awk` batching accepts a simple per-file loop first;
  optimize only if the selected NFR measurement fails.
- Runner batch re-exec is fixed-size and tunable through an existing/configured
  runner option, not a new service.
- MCP/LSP startup measurement includes wrapper and protocol handshake; request
  latency measures correlated warm calls after startup.

## Migration order

1. Pure classifiers and source-contract tests.
2. Security/root correctness fixes.
3. Provenance deployment and launcher routing.
4. Real qualification/performance evidence.
5. Remove obsolete handlers/spec duplicates only after all callers move.
