# Tree-wide POSIX-shell spawn gaps and seed process debt (2026-09-19 sweep)

Date: 2026-09-19
Lane: suite-2026-09-18 (Windows, seed binary)

## Environment-blocked specs (POSIX-only fixtures/spawns on the Windows seed)

1. `src/lib/nogc_async_mut/mcp/fileio_server.spl:380-398` — read/write/
   delete/copy/move/append shell out to `cat`/`echo>`/`rm`/`cp`/`mv`.
   Blocks 12 examples of `test/01_unit/app/mcp/fileio_main_spec.spl`.
   Fix direction: native rt_* file probes (same treatment io_runtime.list_dir
   received in 5476c365f98).
2. `src/app/mcp/main_lazy_ctx_tools.spl:753,923` — ctx batch/execute spawn
   `/bin/sh`. Blocks 3 ctx_batch_scale, 2 token_stats, 6 ctx_tools examples.
3. devhub cmd_github (19 fake-binary examples), cmd_tasks (22), email_cmd
   (13) — `#!/bin/sh` stub binaries cannot exec on the Windows seed
   (extensionless scripts and .cmd shims both fail; the sources spawn the
   tools directly so there is no interpreter seam).
4. Child-process specs running `bin/simple.exe <subcommand>`: ledgered in
   check_worker_seed_interpreter_gap_2026-09-19.md.

## Seed runtime debt (affects any spec doing process spawns)

- `process_run` / `process_run_bounded` execute the child command TWICE and
  return the second result (both `unsafe` lanes fire). Worked around in
  devhub/wiki_git.spl with double-run tolerance; the runtime fix belongs in
  the process facade layer.
- `me` and `case` are reserved words on this seed (specs using them as
  identifiers fail to parse).
- String literals process backslash escapes; Windows paths in specs must use
  forward slashes.
- s[i]/char_count() are char-based while len()/slices are byte-based on the
  seed — multibyte indexing code must walk char arrays (fixed in
  src/app/devhub/convert_storage.spl; SAME BUG still present in
  src/app/itf/convert_storage.spl).

## Production gaps found while triaging

- `src/app/cache_gateway/{gateway,main,publish}.spl` import
  `compiler.driver.cache.remote.namespace_policy` — the module file was
  never committed (squash-merge e274cd33719 added the imports). HEAD does
  not compile the cache_gateway app.
- Commit 81cc36a0048 dropped ponytail ladder mode, diff input, and
  memo/telemetry wiring without updating specs (specs re-pinned in
  12bd321c239). Decide separately whether to restore the wiring.

## Merge e274cd33719 regression pattern

The "merge all share-history worktree branches" commit repeatedly resolved
conflicts by taking pre-triage versions, clobbering 82bf2cfe907 (llm_caret
repairs — restored in 1c3a87982e3) and aff29a24dfe (llm_runtime vllm
support — restored in 0ea76a026ac) plus doc_coverage oracles. Other repairs
from those commits may still be missing; when a spec pins behavior that
used to pass, diff against those commits first.

## Addendum 2026-09-19 (shard3 sweep): seed test-mode neuters ALL child spawns

Reproduced while triaging the ~100-file `*_log_modes_spec` cluster
(`test/02_integration/app/env_log_modes_spec.spl` et al.):

- `rt_process_run("/bin/sh", ["-c", "echo probe_out"])` returns
  `(code=-1, out="", err="")` when executed under
  `bin/simple.exe test <spec> --mode=interpreter`.
- The IDENTICAL probe under `bin/simple.exe run probe.spl` returns
  `(code=0, out="probe_out\n")`.
- A nested `$(pwd)`-based `bin/simple run src/app/env/main.spl --help`
  also works under `run` (code=0, ~700 chars of help) but returns -1
  under `test`.

Conclusion: the seed's test-mode harness fails/neuters every
`rt_process_run` child spawn on Windows with the -1 sentinel, independent
of what is being spawned. This is the single root cause behind the
~100 `*_log_modes_spec` failures and a large share of the scv_*/editor_*
integration FAILs that shell out to the CLI — they are all one ledger
class, not per-spec bugs.

Not fixable in the suite-fix lane: the failing binary is the shared Rust
seed at `/c/Users/ormas/dev/simple/bin/simple.exe` (other lanes' build
output; must not be rebuilt/replaced here), and the project direction is
to replace the seed with the pure-Simple binary rather than patch the
seed runtime. Fix direction: pure-Simple test runner must wire
rt_process_run through in test mode (parity with run mode).

## Cross-reference 2026-09-19 (enum_single_field_payload triage)

Also blocks `test/01_unit/compiler/interpreter/enum_single_field_payload_spec.spl`
(4/4 examples FAIL, every assertion `expected <empty> to contain PASS ...`):
the spec's oracle is a subprocess probe
(`test/01_unit/compiler/interpreter/probe_enum_single_field_payload.spl`
spawned via `std.io_runtime.process_run`), and the neutered test-mode spawn
returns empty output. Verified the pinned tree behavior is correct: the
probe prints `ENUM_PAYLOAD PROBE: ALL PASS` under `bin/simple.exe run` in
both `SIMPLE_EXECUTION_MODE=jit` and `=interpreter`. Not the original
`interp_run_enum_single_field_payload_corrupt_2026-06-15.md` defect (closed,
run-path only) — pure seed test-mode spawn debt.

## Cross-reference 2026-09-19 (dict_class_value_identity triage)

Also blocks `test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl`
(4/4 examples FAIL, `expected <empty> to contain PASS ...`): oracle is the
subprocess probe
`test/01_unit/compiler/interpreter/probe_dict_class_value_identity.spl`
spawned via `std.io_runtime.process_run("sh", ["-c", "...bin/simple run <probe>..."])`,
same shape as the enum_single_field_payload cross-reference above. Verified on
this lane's Windows seed (`/c/Users/ormas/dev/simple/bin/simple.exe`):

- Probe standalone: `SIMPLE_EXECUTION_MODE=jit bin/simple run <probe>` prints
  all 7 `PASS` lines + `DICT_CLASS_IDENTITY PROBE: ALL PASS`;
  `SIMPLE_EXECUTION_MODE=interpreter` fails 6 of 7 (unchanged, tracked in
  `interp_dict_class_value_copy_on_get_mutation_loss_2026-07-06.md` —
  interpreter dict class-value copy is deliberately unfixed seed debt).
- The same probe spawned from a spec body under
  `bin/simple.exe test <spec> --mode=interpreter` returns EMPTY or
  first-line-only stdout (`out.0`, exit reported 0) — nondeterministic
  partial pipe capture of the heavy nested `bin/simple run` child.
  Light child spawns from the same spec body (`echo`, `bin/simple
  --version`) capture fine, so the defect is specific to the heavy
  nested compile-and-run child, matching
  `nested_run_subprocess_empty_stdout_under_test_2026-07-20.md`.

Pinned tree behavior is correct on the JIT engine; the spec is red purely
from seed test-mode spawn/capture debt. Spec and probe left unmodified.
