# CLI external-compile delegation fork bomb (`compile --backend=vhdl`)

- **Date:** 2026-07-24
- **Severity:** critical (system-wide resource exhaustion; ~35k leaked
  processes; killed an unrelated Vivado implementation run at checkpoint
  write; also the cause of the earlier "generate-script hang at 0% CPU")
- **Status:** root fix implemented in `.spl` (requires redeploy to reach
  `bin/release/*` binaries); wrapper guard retained as defense-in-depth

## Anatomy

`simple compile <f> --backend=vhdl` in the full self-hosted CLI:

1. `src/compiler/80.driver/driver_public_compile.spl` `aot_vhdl_file()` tries
   the in-process VHDL subset; on failure falls through to
   `_run_compile_to_path(path, output, ["--backend=vhdl"])`.
2. `_run_compile_to_path` calls `find_simple_binary()` which (like
   `src/app/mcp/main.spl:53`) returns **`bin/release/simple`** — a wrapper
   script that `exec`s the SAME full CLI.
3. The child repeats 1-2. No recursion guard on this path (the
   `SIMPLE_FRONTEND_DELEGATED` / self-exec guards in `cli_ops.spl` are not
   consulted by `_run_compile_to_path`, and `SIMPLE_BOOTSTRAP_DRIVER` is
   ignored by `find_simple_binary`) → unbounded `sh → simple → sh → simple…`
   chain.

Observed: 34,835 `sh` + 34,828 `simple` processes (a single linear chain that
had survived for days, orphaned), free RAM down to 1.5 GB, `fork: retry:
Resource temporarily unavailable` shell errors, and Vivado `impl_1` failing
with `report_power failed` / `Failed to create design checkpoint`.

## Cleanup used

`pkill -f 'backend=vhd[l]'` (bracketed class avoids the killer's own cmdline
self-match). 98,635 → 832 system processes.

## Mitigation (in place, tracked)

`bin/release/simple` wrapper now carries a re-entry flag: first pass exports
`SIMPLE_WRAPPER_REENTERED=1` and execs the CLI; any re-entry execs the Rust
seed instead (which really implements `--backend=vhdl` and never delegates).
Verified: the VHDL compile now holds a flat 3 processes and terminates
(rc=1 with the seed's own pre-existing VHDL-backend error — a separate, known
degradation; both FPGA lanes bypass it).

## Root fix (implemented, `.spl`, requires redeploy to take effect)

`src/compiler/80.driver/driver_public_shared.spl` now has a delegation-loop
guard consulted by every external-compile spawn in
`src/compiler/80.driver/driver_public_compile.spl` (`compile_file`,
`compile_to_smf`, `jit_file`, `check_file`, `_run_compile_to_path` — which
covers `aot_file`/`aot_c_file`/`aot_llvm_file`/`aot_vhdl_file`/etc.) and in
`_build_native_shared_library` in the same shared module:

- **Marker guard (the actual root fix for the wrapper-mediated loop):**
  before spawning, `check_compile_delegation_guard(op_desc, resolved_bin)`
  reads the `SIMPLE_COMPILE_DELEGATED` env var. If already `"1"` (set by a
  parent in this same delegation chain via `mark_compile_delegated()` right
  before its own spawn), the spawn is refused and a
  `CompileResult.RuntimeError` / `Err(...)` is returned instead:
  `"compile delegation loop detected: external fallback resolves to this
  same CLI; {op_desc} not supported in-process"`. Since `rt_process_run`
  inherits the parent's environment (the runtime never calls
  `env_clear()`), the marker set via `rt_env_set` on the parent is visible to
  the wrapper's child and to any grandchild it execs into — this is what
  bounds the `sh → simple → sh → simple…` chain to one hop.
- **Trivial self-reference guard:** `is_same_binary_path(resolved_bin,
  current_exe)` cheaply compares the resolved external binary's path against
  this process's own executable (`readlink -f /proc/self/exe`, no full
  canonicalization round-trip) so a `find_simple_binary()` return of the
  currently-running binary itself (no wrapper hop) is also refused.
- The decision core (`compile_delegation_guard_decision`,
  `compile_delegation_guard_message`, `is_same_binary_path`) is a pure,
  no-I/O function — regression-tested directly without spawning any
  processes: `test/01_unit/compiler/driver/compile_delegation_guard_spec.spl`
  (5 examples, all pass under the self-hosted binary).

Redeploy note: this fix lives in the compiler's own `.spl` source, so it only
takes effect once the self-hosted binary is rebuilt and redeployed to
`bin/release/<triple>/simple` — until then, the deployed binaries still rely
solely on the wrapper-level `SIMPLE_WRAPPER_REENTERED` mitigation described
above.
