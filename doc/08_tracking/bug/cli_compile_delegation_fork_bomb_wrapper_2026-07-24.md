# CLI external-compile delegation fork bomb (`compile --backend=vhdl`)

- **Date:** 2026-07-24
- **Severity:** critical (system-wide resource exhaustion; ~35k leaked
  processes; killed an unrelated Vivado implementation run at checkpoint
  write; also the cause of the earlier "generate-script hang at 0% CPU")
- **Status:** mitigated at the wrapper; root fix pending in `.spl`

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

## Root fix direction (`.spl`, requires redeploy to take effect)

- `find_simple_binary()` must never resolve to the current executable or a
  wrapper for it (compare resolved/inode, honor `SIMPLE_BOOTSTRAP_DRIVER`
  first, prefer the seed sibling).
- `_run_compile_to_path` must carry a depth/loop guard (refuse to spawn when
  an external-compile marker env is already set).
- Add a regression test: `compile --backend=vhdl` on a file that defeats the
  subset fallback must terminate with bounded process count.
