<!-- codex-design -->
# Agent tasks: compiler loader script cross-language performance

Status: decision-ready breakdown; requirement selection and final architecture
review remain mandatory.

## Shared contracts defined before parallel work

- Product owners: `resolve_module_path`, `module_resolve_cache_reset`,
  `rt_file_exists_probe_begin/end`, packed-byte receiver/place mutation owners,
  and a call-scoped foreign byte descriptor.
- Manual step phrases are the nine ordered phrases in
  `doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md`.
- Canonical checkers are `scripts/check/check-file-exists-probe-c.shs` and
  `scripts/check/check-cross-language-perf.shs`.
- Any newly scaffolded SSpec oracle must use `assert(false)` or `fail(...)`
  until real evidence is implemented; placeholder passes are forbidden.

## Parallel lanes

| Lane | Ownership | Files/scope | Completion receipt |
|---|---|---|---|
| PBL semantics | compiler interpreter owner | packed concat/clone/equality and projected-place tests/owners | focused deliberate-red and green Rust test logs |
| Foreign capability | interpreter SFFI owner | descriptor bounds, input-only access, call-scoped lifetime/escape tests | focused deliberate-red and green capability test log |
| Loader/probe | pure-Simple loader + runtime owner | cache keys/reset and native/interpreter probe providers | resolver evidence and C lifecycle selfcheck |
| Harness/manual | performance/SPipe owner | admission, bounded execution, retained schema, executable spec/manual | contract logs; admitted run only when prerequisite exists |
| Bootstrap prerequisite | pure-Simple compiler-driver owner | preserved Stage 2 lineage and Stage 3 corruption | one bounded Stage 3 verdict and provenance artifacts |
| Research/design | research/design owner | option selection, final REQ/NFR, accepted architecture/design | explicit user choice and final reviewer receipt |

Lower-model sidecars: **N/A for acceptance decisions**. Parallel agents may own
the bounded implementation/evidence lanes above, but the merge owner reconciles
shared files and the best available normal/highest-capability reviewer accepts
the combined requirements, exclusions, generated manual, and done marks.

## Integration ownership

Merge owner: compiler-loader performance lane owner. The merge owner preserves
unrelated dirty files, runs each acceptance command once, allows at most three
distinct fix cycles, commits only intentional files, and serializes the final
detached-HEAD integration using the lane's required lock.

Final reviewer: highest-capability reviewer after explicit user selection.
Stage 2/3 evidence must remain labeled; it cannot be promoted into a missing
deployed-cli result.
