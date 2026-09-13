# Dead `?? fallback` on the TOTAL `env_get`: 34 sites in `src/` silently get `""`

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-4, `work/bootstrap-full-2-2026-09-12`
- Severity: silent wrong value (no diagnostic, no crash). One instance
  rejected a Stage-2 bootstrap for a full run.
- Binary: `bin/simple` -> `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  (Rust seed), sha256 `3d120a6f9ab5704b...`

## The trap

`std.nogc_sync_mut.io.env_ops.env_get` is TOTAL:

    src/lib/nogc_sync_mut/io/env_ops.spl:48
    fn env_get(key: text) -> text:
        env_get_opt(key) ?? ""

It reports an unset variable as `""`, never nil. So `env_get(K) ?? default`
can never take `default` -- the caller silently receives `""`. The sibling
`std.io_runtime.env_get_opt` (`src/lib/nogc_sync_mut/io_runtime.spl:386`) is
nil-for-unset by construction and its own doc comment already says to prefer
it and to migrate old `?? default` sites; nothing enforces that.

## Measured population (2026-09-13, owned code only)

`env_get("NAME") ?? <expr>` in `src/**/*.spl`: **539** sites. Most use `""` as
the fallback and are therefore harmless (`"" -> ""`). **34** use a non-empty
fallback and are live defects. Three are in the compiler driver:

    src/compiler/80.driver/build_log.spl              env_get("PWD") ?? "."
    src/compiler/80.driver/driver_source_pipeline_loading.spl
        env_get("SIMPLE_BUILD_ORDINAL") ?? "0"
        env_get("SIMPLE_COMPILER_ARTIFACT_OWNER") ?? "local-compiler-owner"
        env_get("SIMPLE_DEMAND_COMPILE_PROFILE") ?? "compiler"

The rest are in `src/app/**`, `src/os/**` and `src/lib/nogc_sync_mut/src/**`
(e.g. `env_get("SIMPLE_BIN") ?? "bin/simple"`, `env_get("HOME") ?? "/home/user"`,
`env_get("TMPDIR") ?? "/tmp"`). Reproduce the census with:

    grep -rnoP 'env_get\("[A-Z0-9_]+"\)\s*\?\?\s*(?!"")\S' src/ --include=*.spl \
      | grep -v env_get_opt

## Why it is worth a record rather than a sweep

The instance this lane hit --
`src/compiler/80.driver/driver_orchestration.spl` reading
`SIMPLE_NATIVE_NOOP_CACHE_ROOT` / `SIMPLE_NATIVE_NOOP_FINAL_OUTPUT` -- made the
zero-work native request unidentifiable on every ordinary build and rejected
Stage 2 with `native no-op receipt publication failed: request-invalid`. It is
fixed in that file. The other 34 are NOT fixed here: each needs its own
judgement about whether `""` or the written default is the intended value, and
flipping 34 never-observed behaviours inside a bootstrap lane launders
regressions.

## Suggested resolution

A lint rule (or a ratchet like `check-no-direct-rt.shs`) that flags
`env_get(...) ?? <non-empty>` and directs the author to `env_get_opt`. The
fallback-is-`""` sites are already no-ops and can stay, but they are the noise
that hides the 34.

## Related — and a correction

`env_get` additionally has **4 co-compiled definitions across 2 signatures**
(`(text)->Optional(text)` vs `(text)->text`); the seed warns
`compiler_cross_module_private_symbol_collision` on every run and says call
sites resolve by exact arg-type match, "falling back to the last definition when
types are ambiguous". That is a real hazard and worth its own record.

It is **not** established as the cause of anything here, and an earlier draft of
this record said it explained an interpreter/native divergence. It does not.
BOOT-3's receipt states that in the interpreter "the same empty identity runs
PAST the mkdir to `receipt-invalid`" — i.e. the identity was empty in the
interpreter too. The only interpreter/native difference was whether
`rt_dir_create_all` refused the resulting path, and that is now explained
without any dispatch defect: with the cache root AND the identity both empty,
`"{root}/{identity}/generations"` is `"//generations"`, i.e. `/generations` at
the filesystem root. This lane's own spec confirms the uniformity: its first
example asserts `env_get(unset) ?? "fallback" == ""` and PASSES in the
interpreter.
