# Stage-2 sanity's two frontend passes share one object store despite separate `--cache-dir`s

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-6
- Severity: the isolation the gate believes it has, it does not have. It turned
  a second-build defect into a verdict that named `SIMPLE_BOOTSTRAP` as the
  variable, which cost a lane.

## Measured

`scripts/check/lib/bootstrap-stage3-candidate-builder.shs:376-392` runs
`candidate_frontend_smoke` twice — `CANDIDATE_FRONTEND_BOOTSTRAP=0`, then `=1`
only if pass 0 succeeded — inside one subshell that exports a single
`HOME=$sanity_home`.

`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:598` makes a
FRESH `probe_dir=$(mktemp -d ...)` per invocation and passes
`--cache-dir "$probe_dir/cache-hello-world-positional"`, which reads as full
per-pass isolation.

It is not. The in-process driver derives its native cache from
`driver_native_build_cache_dir()`
(`src/compiler/80.driver/driver_aot_native_output.spl:737`), which reads
`SIMPLE_NATIVE_BUILD_CACHE_DIR` and otherwise falls back to
`machine_cache_root()/native-build/v1` — i.e. `$HOME/.cache/simple/v1/projects/<hash>`.
Both passes therefore wrote to
`.../stage2-home/.cache/simple/v1/projects/7dcf7beb.../native-build/v1/se3b0c44.../`
while each believed it had its own cache. The CLI flag is not forwarded to the
in-process build.

Consequence, measured on the real run: pass 0 published
`object.<module>.o` (1080 bytes); pass 1 recompiled the same module into the
same path and failed. The evidence file then reported
`frontend_smoke_bootstrap_mode_status=1` with pass 0 green, which reads as
"bootstrap mode is broken". Reversing the order (BOOT-6, same binary) makes
`SIMPLE_BOOTSTRAP=1` pass and `=0` fail — the variable is ORDER, not bootstrap
mode.

## Not fixed

BOOT-6 fixed the product defect the shared store exposed, deliberately, rather
than the harness: two builds of the same module into one scope must work, and a
user with a persistent `$HOME/.cache` hits exactly this. The harness gap stands
on its own though — a gate whose two passes are not actually isolated cannot
attribute a difference between them to the variable it changed. Either forward
`--cache-dir` into the in-process driver (or set
`SIMPLE_NATIVE_BUILD_CACHE_DIR`), or give each pass its own `HOME`.
