# Windows owned-scope admission: bounded repair evidence

Worktree: `D:/dev/simple-tooling-phase3-check-20261025`, based on release/1.0.0.
Producer remains the local Stage 3 compiler with SHA-256
`13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.
No Rust-seed fallback or relaxed resource/deadline policy was used.

## Root repairs and evidence

`resource_scope.spl` imports total-text `env_ops.env_get`, but coalesced its
TMPDIR/TEMP result as though it were optional. Explicit empty-string fallback
removed the observed `owned Windows temporary root unavailable` failure.
The rebuilt native runner then reached `owned Windows process admission failed`.

The redirected process owner now provides a checked `Result<i64, text>` admission
API in both configured platform branches. Its existing integer-token APIs remain
adapters with unchanged signatures. Resource scope releases the governor slot
on checked error and retains the actual admission reason. Successful wait,
collection, cancellation, quarantine and capture cleanup paths are unchanged.
Array append results are retained explicitly for environment, image and lease
storage. Independent static review found no new P0/P1; this is not runtime PASS.

The smaller native probe identified capture-directory creation as the next
failure. Ordinary directory creation on the workspace drive succeeded, but the
generated native `C:\Users\...\Temp\simple-owned-*.out.scope` path failed.
`rt_dir_create_cpath` had its own recursive walk that attempted mkdir on `C:`.
It now reuses the existing `rt_dir_create_all_cpath` worker, which skips drive
roots and preserves POSIX backslashes as filename bytes.

The final probe compiled and progressed beyond capture-directory creation to
`invalid environment assignment`. This proves progress through the directory
boundary; it does not prove child launch. The validating owner rejects an
assignment when `assignment.split("=")` has fewer than two fields or an empty
first field (`windows_process_owner.spl`, request validation). No environment
values were dumped. Next diagnosis must include valid empty values (`KEY=`),
values containing `=`, hidden Windows drive entries, and native snapshot/tuple
representation, without logging secrets or weakening environment validation.

## Six-attempt ledger — exhausted

1. Original native runner build: actual SSpec invocation failed at temporary-root
   admission; zero example passes.
2. Explicit TMPDIR/TEMP fallback; rebuilt runner: actual SSpec invocation advanced
   to generic process-admission failure, before test compilation.
3. Small owned-scope probe: PowerShell accidentally added a UTF-8 BOM, rejected
   at parsing. Fixture encoding was corrected explicitly.
4. Checked admission and retained append results: probe compiled; execution
   reported private capture-directory creation failure.
5. Added bounded path/directory diagnostics: probe compiled; workspace create,
   existence and nonrecursive removal passed; the generated TEMP path failed.
6. Shared recursive C directory worker; explicit `SIMPLE_PROJECT_ROOT` binding:
   probe compiled; directory boundary passed and environment validation rejected.

Do not reset this resource-owner repair budget by changing worktrees, output
names, or feature labels. Retain remaining failure rather than repeating it.

Artifacts are in the same worktree: `test_runner.tempfix.native.log`,
`md_lsp.sspec.tempfix.log`, `owned_scope_probe.cycle4.native.log`,
`owned_scope_probe.cycle5.native.log`, `owned_scope_probe.cycle6.native.log`,
`owned_scope_probe.diagnostic.run.log`, and `owned_scope_probe.final.run.log`.
Probe sources and executables are under `build/tooling-check/`; they are
diagnostic artifacts, not four executed Markdown examples or SSpec qualification.

The production-importing owned child regression was added to
`test/01_unit/lib/nogc_sync_mut/io/resource_scope_child_spawn_spec.spl`.
It remains UNRUN. Full CLI check gates, runtime/native smokes, representative
latency/RSS, actual SSpec runs and generated manuals are still required.

STATUS: FAIL — directory and error-evidence repairs are real; child admission
and SSpec execution remain blocked. No release admission or merged PR claimed.
