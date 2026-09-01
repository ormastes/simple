# Interpreter I/O owner correction receipt

- Compiler: `/mnt/data/worktrees/goal-cache-shadow-freeze/build/bootstrap/versioned-backend/stage2/by-sha/04ce32fa8d913889e33db1670bd11de08bca6d85e375ca21c1970b2ee6deb397/simple`
- Compiler SHA-256: `04ce32fa8d913889e33db1670bd11de08bca6d85e375ca21c1970b2ee6deb397`
- Admitted capsule identity: `2a85ded2acecbf79359e8db486877802e1026785ce0078eafcc258b42fe92a80`
- Admitted receipt: `/mnt/data/worktrees/goal-cache-shadow-freeze/build/test-logs/phase2-direct-build-9f83ba71c2c-20260829/terminal.receipt.md`
- Cache scope: `SIMPLE_CACHE_SCOPE=interpreter_io_fs_import_correction`
- Temporary/output root: `/mnt/data/simple-cache/interpreter-io-fs-import-correction`
- Stub fallback: disabled with `SIMPLE_NO_STUB_FALLBACK=1`

## Focused strict fixture

The final strict entry-closure build compiled the I/O owner fixture with 1
compiled module, 38 cached modules, and 0 failures. The retained runtime run
piped `fixture-stdin` to the binary and exited 0 after exercising file
existence/read, stdin, stdout/flush, and diagnostic stdout/stderr calls.

- Build: `focused-strict-build-cycle3.log` — PASS
- Runtime: `focused-runtime-stdin.log` — PASS

Cycle 1 used an over-broad source scan and stopped before HIR on an unrelated
sanitized module-name collision. Cycle 2 established the entry-closure command.
Cycle 3 is the final fixture and passed; no further retry was performed.

## Full interpreter limitation

`interpreter-strict-build.log` contains the strict entry-closure build of
`src/app/interpreter/main.spl`. It reports no unresolved `io` or `fs` symbol and
advances to four unrelated existing LLVM semantic failures: undeclared `Box`
in `ast_convert_expr.spl` and `ast_convert_pattern.spl`, undeclared `Dict` in
`core/environment.spl`, and undeclared `eval_control` in `core/eval.spl`.
Therefore this receipt proves the I/O regression is removed but does not claim
that the complete interpreter native build is green.

## Runtime facade guards

- `direct-env-working.log` — `STATUS: PASS direct-env-runtime-guard`
- `direct-env-staged.log` — `STATUS: PASS direct-env-runtime-guard`
