# Per-file worker unit: per-module MIR cost scales with the unit's HIR closure

- **Found:** 2026-11-28, manual full-CLI build with the admitted Stage 2 compiler
  (`c7c151462a20…`, source `38cb1016a31`, aarch64 Linux, llvm backend, `--mode dynload`).
- **Status:** open (performance). No source workaround applied.

## Symptom

`SIMPLE_FILE_WORKER_BATCH` larger than the adaptive 16 does not amortise the
per-unit fixed cost; it makes every module slower.

| run | batch | unit HIR closure | `[mir-slow]` for the same module |
|---|---|---|---|
| official `compiler_cli_build` | 16 | 50-70 | `compiler.frontend.core._Ast.decl_nodes` 2.5 s, `lexer_struct` 2.3 s, `hir_lowering.types` 2.9 s |
| manual run1 | 256 | 478 | 17.2 s, 17.6 s, 15.6 s |

In run1 every module, including small ones (`lib.common.binary_inspect`,
`lib.common.base_encoding.utilities`), cost 12-17 s of single-threaded MIR
lowering, flat across the unit (10-module means 12.1, 15.0, 14.4, 13.9, 14.1,
14.0 s). 32 modules took ~570 s (MIR ~450 s + codegen ~100 s); the official
run lowers 16 modules in ~48 s.

The unit's fixed part also grows with the closure: parse+HIR for the
256-claim unit took 16-19 min (closure 478) against ~4 min at closure ~60.

## Measurements of the MIR child (run1, 22 GB RSS, 17.5 GB brk heap)

- ~84,000 minor faults/s, user:system CPU about 1:1.
- `LD_PRELOAD` no-op `malloc_trim` + `MALLOC_TRIM_THRESHOLD_=1GiB` (run2):
  faults fell to ~10,000/s and system time to ~0, but the same modules got
  SLOWER (20-28 s) and the tree peak rose to 42 GB. The trim is not the cause;
  the shim is not a usable workaround and was dropped.

So the cost is user-time work proportional to the loaded closure, done once
per lowered module (candidates, unverified: the consumer-local trait lookup
tables "rebuilt at the start of every lower_module", provider table
relocation/retraction, transient scope promotion).

## Consequence

Throughput of one worker is bounded near 11-12 s/module whatever the batch
(batch 16: ~363 s fixed per unit; batch 256: ~15 s/module), i.e. 13 h+ for the
4,220-module full CLI on one worker. More workers need ~22-25 GB each because
every unit child reloads all 7,194 sources.

## Next step

Enable the MIR section profile (`mir_section_profile_mark`) on one 256-claim
unit and find which section carries the closure-proportional term.
