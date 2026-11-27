# Interpreter binds sosix_proc_usage to a body that cannot be reached from source (2026-11-10)

**Status:** open. Blocks executing the live path of `sosix_proc_usage` (and
likely other sosix run-path consumers) under `bin/simple test` and
`bin/simple run` on Windows; the phase-1 seed is the binary of record here.

## Symptom

Calling `sosix_proc_usage(<live pid>)` raises

```
semantic: unknown extern function: rt_process_run_bounded_bytes
```

while `sosix_proc_usage(<dead pid>)` and `sosix_proc_usage(<= 0)` return
honestly (`valid: false`) and `sosix_platform()` works in the same program.

## Why it cannot be a source-level call

The only `process_run_bounded_bytes` call site in `src/lib` is
`sosix_run_path_checked`'s Windows branch
(`src/lib/nogc_async_mut/sosix/host_facade.spl`), reachable only via
`sosix_run`. The shipped `sosix_proc_usage` Windows lane reads tasklist via
`process_run_bounded` (the text provider, interpreter-registered), and its
dead-pid paths prove the lane itself executes. An inline, statement-for-
statement replication of the same lane inside a probe program runs correctly
against pid 4 (`"System","4","Services","0","55,684 K"` -> 54 MiB), so the
logic and the externs it uses are fine.

Conclusion: the imported `sosix_proc_usage` symbol dispatches to a co-compiled
definition whose body still contains the bytes-capture call — the same
duplicate-definition binding family as
`module_var_write_lost_when_rhs_method_reads_me_2026-09-05.md` and
`process_exists_proc_only_and_piped_pids_invisible_2026-09-05.md` ("JIT call
sites resolve by exact arg-type match, falling back to the last definition
when types are ambiguous — a fallback hit may still dispatch to the wrong
one"). The live branch compiles a unit the interpreter cannot link; the
dead branches never compile that unit, which is why they stay green.

## Repro

```text
bin/simple.exe run build/nb/fixtures/probe_lane.spl
  -> platform=windows
  -> error: semantic: unknown extern function: rt_process_run_bounded_bytes
```

(same under `bin/simple.exe test <spec> --mode=interpreter`).

## Consequence

The Windows tasklist lane added for `sosix_proc_usage` is parser-verified and
shell-verified but cannot be executed through the imported symbol until this
binding defect is fixed; `proc_usage_spec.spl` therefore only asserts the
always-alive/dead-pid contract that the harness can run. The `cs` dashboard's
live usage read on Windows inherits the same limitation.
