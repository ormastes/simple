# Stage-3 combined-fix SIGSEGV at parse start: `LayerDagRegistry.edges` field-offset collision (2026-08-07)

## Status: FIXED, landed

## Summary

With Stage 2 unblocked by `983058c5ff39` (dead `struct Mailbox` removal), Stage
3 could run for the first time in the combined-fix chain tracked by
`doc/09_report/compiler/stage3_replay_verification_2026-08-07.md` and
`doc/09_report/compiler/stage3_blocker_tractability_2026-08-07.md`. It
SIGSEGV'd (`rc=139`) ~9 seconds in, at the very start of the "parse" phase,
100% reproducible, single-threaded.

## Root cause

`class LayerDagRegistry` (`src/compiler/35.semantics/layer_dag_checker.spl`,
added 2026-08-07 for the zero-cost-layers M0 milestone) declares a field
`edges: [LayerEdge]`. Two unrelated existing types also declare a field
literally named `edges`, at different field ordinals:

- `struct ImportGraph` (`src/compiler/00.common/dependency/graph.spl:54`) —
  `edges` is field ordinal 0.
- `struct GraphDiagram` (`src/compiler/15.blocks/blocks/value.spl:134`) —
  `edges` is field ordinal 3.
- `class LayerDagRegistry` (new) — `edges` is field ordinal 2.

When the Rust seed built Stage 2 from `origin/main` via
`build/cyc/build_stage2.sh`, its native-build field-offset resolution
collided across these three same-named-but-different-ordinal fields:
`LayerDagRegistry.edges` was assigned the wrong byte offset in the compiled
Stage-2 binary. Stage 2 itself parses fine (the bug is latent — the field is
only read, never in a way that crashes Stage 2's own compilation of itself).
The crash fires the first time Stage-2's *compiled machine code* executes
`layer_registry.edges` at runtime while Stage 2 is compiling Stage 3 — i.e.
while running `flat_ast_to_module()`
(`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:741`,
pre-fix) on the very first Stage-3 source file
(`src/app/cli/bootstrap_main.spl`). The misresolved offset makes the
compiled read treat a small tagged/garbage value as an array pointer,
`SIGSEGV` on `mov 0x8(%rax)` with `rax=0x40`.

This is the same *class* of defect as the borrow-checker field-index
collision fixed in `b9e23914a0e` (`NLLChecker.errors`, `si_addr=0x118`) — a
same-named field colliding across module boundaries in a whole-program
build — but at a **different call site** (this is a Rust-seed struct/class
field-offset resolution collision exposed while building **Stage 2**, not
the pure-Simple borrow-checker `resolve_field_index` tier that `b9e23914a0e`
patched, which only runs inside the *self-hosted* compiler's own MIR
lowering). The pure-Simple fix does not reach this call path.

## Narrowing evidence

Reproduced and bisected in the isolated worktree `/home/ormastes/dev/simple-s3bisect`, pinned to `origin/main` `6a6ee4283a4`:

1. `build_stage2.sh` VER10 → `STAGE2_EXIT=0`, clean 125 MB binary (confirms
   the eighth Mailbox blocker from the prior report is fixed).
2. `run_stage3.sh` VER10 → `STAGE3_EXIT=139`, `WALL=9s`,
   `PROGRESS: phase=parse ... done=0 total=553`. Log: only `timeout: the
   monitored command dumped core` / `Segmentation fault` (no `^error:` —
   confirms a genuine crash, not a masked diagnostic).
3. Launched the identical command directly under `gdb --batch -ex run -ex bt`
   (not attach — `ptrace_scope=1` blocks attach in this environment, direct
   launch is unaffected) with `--threads 1` for a clean single-thread trace:
   ```
   #0 compiler__frontend___FlatAstBridge__module_assembly__flat_ast_to_module
   #1 ...__parse_and_build_module_scoped
   #2 compiler.frontend.frontend.parse_full_frontend_with_scope
   #3 ...CompilerDriver.parse_all_impl
   #4 ...CompilerDriver.compile
   #5 app.cli.bootstrap_main.run_native_build_bootstrap
   #6 main
   ```
   Faulting instruction: `mov 0x8(%rax),%r13` with `rax=0x40` — a near-null
   pointer read one field-offset deeper than a valid arena pointer, right
   after an `and $0xfffffffffffffff8,%rax` untag mask (array-length-read
   codegen pattern for a `for x in arr:` loop).
4. `SIMPLE_COMPILER_TRACE=1` plus temporary `eprint` probes added around
   `flat_ast_to_module`'s post-decl-loop code (`check_layer_dag`, the
   `layer_registry.names` loop, the `layer_registry.edges` loop) narrowed the
   crash to strictly between the "pre-edges-loop" and "post-edges-loop"
   markers — i.e. inside/at entry to
   `for layer_edge in layer_registry.edges:` (pre-fix line 741). The
   `.names` loop (same object, different field, primitive-`text` element
   type) executed cleanly moments earlier, which is what pointed at a
   field-specific offset bug rather than object corruption.
5. Grepped for other `edges:` field declarations project-wide, found the
   three-way collision above. Renamed `LayerDagRegistry.edges` to
   `use_edges` (its only two colliding siblings, `ImportGraph.edges` and
   `GraphDiagram.edges`, are working correctly today and were left
   untouched — smallest blast radius, matches how the ambiguous-`Mailbox`
   blocker was resolved).
6. Rebuilt Stage 2 (VER12) with the rename, reran Stage 3 (S3RUN12):
   `STAGE3_EXIT=0`, `WALL=531s`, progressed through parse, HIR, MIR-lowering,
   and reached `phase=monomorphize` (`tasks_done=4/6`), then LLVM codegen
   (`[bootstrap-real-llvm] count 5765 statics 87`), producing a real linked
   ELF executable (`file`: `ELF 64-bit LSB executable ... dynamically
   linked ... not stripped`) at `build/cyc/S3RUN12/stage3-simple`. The
   SIGSEGV is gone; Stage 3 now runs the full pipeline to completion within
   this replay's scope (note: `run_stage3.sh` compiles only
   `src/app/cli/bootstrap_main.spl`, not a full `--entry-closure` build like
   Stage 2 — it is the project's existing lightweight replay harness, not a
   claim of a complete self-hosted binary equivalent to Stage 2's).

## Fix

`src/compiler/35.semantics/layer_dag_checker.spl`: renamed
`LayerDagRegistry.edges` → `use_edges` (field declaration, constructor,
`declare`/`uses` methods, `edges_from`, `check_declared_upward`). Updated
the one external field-access call site,
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:741`
(`layer_registry.edges` → `layer_registry.use_edges`). No other file
accesses the field directly — `layer_call_wiring.spl`,
`layer_call_direction_checker.spl`, and all specs go through
`LayerDagRegistry.new()` / `.edges_from()` only.

Verified via the four layer-DAG spec files under the interpreter
(`bin/simple test`, run from within the fixed worktree so the edited
sources are live): 32 examples, 0 failures across
`layer_dag_checker_spec.spl`, `layer_call_wiring_spec.spl`,
`layer_call_direction_checker_spec.spl`, `layer_decl_parse_spec.spl`.

## Verdict: pure-Simple workaround, Rust-seed root cause still latent

The **fix landed here is pure-Simple** (a field rename) and is sufficient to
unblock Stage 3. The **underlying defect is in the Rust seed's**
native-build struct/class field-offset resolution
(`src/compiler_rust/compiler/src/...` native-project pipeline) — it resolves
field offsets in a way that can collide across types that share a field name
at different ordinals in a whole-program build. This is the same defect
*class* as `b9e23914a0e`, but that fix lives in pure-Simple code that only
runs inside the self-hosted compiler, so it has no effect on how the Rust
seed compiles Stage 2. The rename here is a workaround for one instance, not
a fix for the seed. Any other same-named, different-ordinal field pair
elsewhere in the whole-program build graph remains a latent risk of the same
class of SIGSEGV — same pattern as the `Mailbox` ambiguous-export blocker
(dormant until something changes what's pulled into a whole-program build).

## Disk space

| | Free on `/` |
|---|---|
| Before | 239G |
| After (VER10/VER11/VER12 stage2 builds + S3RUN10/S3RUN12 stage3 replays) | 239G |

Never approached the 100G abort threshold.

## Files

- `src/compiler/35.semantics/layer_dag_checker.spl` (fix)
- `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` (one call-site update)
- `src/compiler/00.common/dependency/graph.spl` (`ImportGraph.edges`, colliding sibling, untouched — working)
- `src/compiler/15.blocks/blocks/value.spl` (`GraphDiagram.edges`, colliding sibling, untouched — working)

## What was NOT touched

- `/home/ormastes/dev/pub/simple/bin/simple`, `bin/release/**` — untouched.
- No `cargo build`, no `--full-bootstrap`.
- Reproduction and fix both done in the isolated worktree
  `/home/ormastes/dev/simple-s3bisect`.
