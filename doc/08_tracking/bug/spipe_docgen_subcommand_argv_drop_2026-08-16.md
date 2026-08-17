# Bug: Rust seed `spipe-docgen` subcommand drops argv (app sees argc=0)

- **Date:** 2026-08-16
- **Status:** RESOLVED — seed fix landed 2026-08-17, pending redeploy; pure-Simple workaround SHIPPED (see below)
- **Severity:** medium (blocked AC-11 manual regeneration via the documented CLI form)
- **Binary:** Rust seed `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

```bash
bin/simple spipe-docgen test/03_system/app/enterprise/store_app_spec.spl --output /tmp/x --no-index
# → prints spipe-docgen usage, exit 1 (app saw zero args)

bin/simple run src/app/spipe_docgen/spipe_docgen/main.spl <same args>
# → works (rt_cli_get_args() returns 5 entries incl. the script path)
```

Instrumented evidence (2026-08-16): under the subcommand route the app observed
`rt_cli_get_args().len() == 0` AND `rt_cli_arg_count() == 0`; under the `run`
route `rt_cli_get_args()` returned `[main.spl, <spec>, --output, /tmp/x, --no-index]`.

## Dispatch site (Rust seed)

`src/compiler_rust/driver/src/main.rs` — subcommand match (~line 314) routes
`spipe-docgen` to file delegation (~lines 753-764,
`app_path: "src/app/spipe_docgen/main.spl"`). The delegation branch at
~line 1364 builds:

```rust
if app_relative_path == "src/app/spipe_docgen/main.spl" {
    let mut full_args = vec![path.to_string_lossy().to_string()];
    full_args.extend(args.iter().skip(1).cloned());
    return Some(run_file_with_args(&path, gc_log, gc_off, full_args));
}
```

`full_args` IS correct at this point. The loss happens below
`run_file_with_args` (`src/compiler_rust/driver/src/cli/basic.rs:320`): the
runner path taken for the delegated invocation never publishes the `args`
vector into the runtime CLI-args storage that backs `rt_cli_get_args()` /
`rt_cli_arg_count()` (`runtime/src/value/cli_sffi.rs` → `rt_get_args()`
PROGRAM_ARGS mutex / `args::cli_arg_*`), so the interpreted app reads an empty
array. The `run` route does publish them, hence the asymmetry. Contrast: the
`sffi_gen` and `play` delegations work around exactly this by smuggling args
through the `SIMPLE_FORCE_ARGS` env var (main.rs ~1350, ~1396) — evidence this
hole is known seed behavior.

## Suggested seed fix (NOT applied — pure-Simple-only policy for this lane)

In `run_file_with_args` (or the runner's interpreted/JIT entry), call
`rt_set_args(full_args)` before executing the file, so PROGRAM_ARGS matches
what the delegation site built. Alternatively use the existing
`SIMPLE_FORCE_ARGS` mechanism as done for `sffi_gen`/`play`.

## Pure-Simple workaround (shipped 2026-08-16)

`src/app/spipe_docgen/spipe_docgen/main.spl` `main()` now falls back, when
`rt_cli_get_args()` returns <=1 entries, to reading `/proc/self/cmdline`
(NUL-separated true process argv) and re-deriving the args
(`args_from_proc_cmdline()`); `run_spipe_docgen` already skips a leading
`spipe-docgen`/`spipe_docgen` token. Verified: subcommand form now exits 0
with `DONE Generated 1 docs (... 0 stubs)`; the `run` form is unchanged.
Limitation: the fallback is Linux-procfs-specific; on other platforms the
subcommand form still shows usage until the seed fix lands — use the `run`
form there.

## RESOLVED — seed fix landed, pending redeploy (2026-08-17)
Seed-side fix applied per the suggestion above:
`src/compiler_rust/driver/src/cli/basic.rs` `run_file_with_args()` now calls
`simple_runtime::value::rt_set_args_vec(&args)` (guarded on non-empty args)
before executing the file, so every delegated subcommand route publishes its
argv into the PROGRAM_ARGS storage backing `rt_cli_get_args()` /
`rt_cli_arg_count()` — the same publisher the `run` route uses
(`driver/src/exec_core.rs:733/747/918`). This fixes the asymmetry for
`spipe-docgen` and every other delegation that reaches `run_file_with_args`
without a publisher, on all platforms (not just Linux procfs).

Verification: `cargo check --release --bin simple` passes with the change
(isolated CARGO_TARGET_DIR; deployed binaries untouched — a full bootstrap was
running concurrently, so **the fix is pending seed rebuild/redeploy**).
Behavioral verification today used the shipped pure-Simple procfs fallback:
`timeout 120 bin/simple spipe-docgen test/03_system/app/enterprise/store_app_spec.spl
--output <tmp> --no-index` → `DONE Generated 1 docs`, RC=0. After the next
seed rebuild, the fallback should no longer trigger (args arrive via
PROGRAM_ARGS); the fallback remains as harmless belt-and-braces. Status:
**RESOLVED (pending redeploy)**.
