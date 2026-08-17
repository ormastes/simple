# borrow_check Layer Expert

## Role

Own layer-specific process knowledge for the borrow checker
(`src/compiler/55.borrow/`). This layer consumes MIR (see
[layer_expert/mir_lowering/skill.md](../mir_lowering/skill.md)) and produces
use-after-move / non-lexical-lifetime diagnostics for `Isolated`-typed
(`iso`) values. It runs after MIR lowering and before backend codegen, on all
three pipeline shapes (JIT, VHDL, AOT) — not AOT-only.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/IMPL.md)

## Layer Links

- Detection core: [src/compiler/55.borrow/borrow_check/mod.spl](../../../../src/compiler/55.borrow/borrow_check/mod.spl)
  (`analyze_instruction`, `analyze_mir_borrows`, `analyze_terminator`).
- NLL forward propagation: [src/compiler/55.borrow/borrow_check/borrow_graph.spl](../../../../src/compiler/55.borrow/borrow_check/borrow_graph.spl)
  (`moved_now` state, comment at `:447` describes a superseded design — see
  Gotchas).
- Move emission (upstream, in `50.mir`): [layer_expert/mir_lowering/skill.md](../mir_lowering/skill.md#iso-ownership-emit_move-had-exactly-one-caller-before-6a53442f-2026-08-06).
- Call sites (three, not just AOT): `80.driver/driver_pipeline_execution.spl:21`
  (JIT), `driver_orchestration.spl:238` (VHDL), `driver_aot_pipeline.spl:97`
  (AOT).
- Unit specs: `test/01_unit/compiler/borrow/` — `borrow_check_spec.spl`
  (11/11, hand-built MIR), `iso_move_pipeline_spec.spl` (3/3, hand-built HIR),
  `iso_move_sites_spec.spl` (2/2), `iso_move_assign_field_spec.spl` (8/8, 4
  sites x iso/non-iso), `iso_use_after_move_e2e_spec.spl` (4/4, real source
  text through parse→HIR→MIR→borrow check), `iso_parse_pipeline_spec.spl`
  (3/3).
- Feature-level picture (end-to-end, user-facing status):
  [feature_expert/iso_ownership/skill.md](../../feature_expert/iso_ownership/skill.md).

## Known Patterns (2026-08-06 — landed `63dc29b1`)

### Call arguments and terminators produced no use-facts

`analyze_instruction` only recorded use-facts in its `Copy`/`Move` arms;
`MirInstKind.Call` fell through to `case _: pass_do_nothing`. Call arguments
ride as bare `MirOperand`s and never become separate Copy/Move instructions,
so a moved value passed to a function (`f(x)` after moving `x`) produced NO
use-fact — even though the identical misuse via a let-binding was caught.
Fixed with a `case Call(dest, func, args)` arm plus a
`me record_operand_use(op, nll, point)` helper that both new call sites (see
below) share.

Separately, `analyze_mir_borrows` walked only `mir_block.instructions` and
never the block's TERMINATOR, so `return x` after a move was equally
invisible. Now calls `analyze_terminator` for `Ret`/`If`/`Switch`/
`CallTerminator`. **The terminator gets its own program point, one past the
block's last instruction** — reusing the last instruction's point would make
a terminator use look concurrent with that instruction instead of strictly
after it, which matters for point-ordered move/liveness facts. Don't collapse
that extra point as a "cleanup" in a future refactor.

## Gotchas

1. **"move-then-use is undetectable by construction" is STALE.** SF1
   (2026-07-28) added forward propagation via `moved_now` at
   `borrow_graph.spl:459`; the design-note comment at `:447` describes the
   OLD design that was replaced. If you find code or docs still citing the
   old limitation, it needs updating, not trusting.
2. **Three call sites, not one.** `borrow_check()` is invoked from
   `driver_pipeline_execution.spl:21` (JIT), `driver_orchestration.spl:238`
   (VHDL), and `driver_aot_pipeline.spl:97` (AOT). Count call sites by
   grepping the CALL itself, not a keyword inside files you suspect house it
   — an AOT-only assumption here has been wrong before.
3. **Detection and emission are independent layers.** A use-fact here is
   worthless without a Move instruction from `50.mir` to detect, and a Move
   instruction is worthless without a use-fact consumer here. Verify a fix by
   isolating: disable one side alone and confirm only its own test case
   regresses. See mir_lowering's Move-emission section for the sites that
   feed this layer.
4. **Nothing here reaches deployed users yet.** `bin/simple` is the Rust
   seed, which has ZERO borrow-check code (`grep -rln "borrow_check"
   src/compiler_rust/driver/src/` → no hits), and stage-3 self-host is
   blocked (`.claude/rules/bootstrap.md`;
   `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`).
   Rank clearing that blocker above further checker work — otherwise this
   layer's fixes stay compiler-source-only, exercised solely by
   `bin/simple test`'s interpreter path.

## Verification Practice

- Compiler `.spl` edits under `src/compiler/**` are LIVE under `bin/simple
  test` (interpreter loads source directly) — no bootstrap rebuild needed to
  iterate here. That says nothing about the JIT/native path.
- Loop: `timeout 900 bin/simple test <spec> --no-cache --no-cover-check`, then
  grep the verdict line (`^Results:`) — the tail is flooded with lint/gc
  warnings and misreads as "no tests ran". One spec file at a time; directory
  runs race a shared test DB.
- Sabotage-probe every change: break it, confirm RED, revert, confirm GREEN.

## Update Rule

After changes to detection (`mod.spl`, `borrow_graph.spl`), the NLL model, or
call-site wiring, refresh this skill with new patterns, call-site counts, and
regression findings.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`

## Stage 3 `native-build` SIGSEGV lands in THIS layer (2026-08-16)

The self-hosted bootstrap compiler cannot compile a three-line hello world —
`compile --format=smf` and `native-build` both exit 139. The crash is in
**`aot:borrow_check`**, post-MIR-lowering and pre-codegen. Own it here.

Pinned two independent ways on the *stripped* artifact (md5 `2244f18ce2e6…`),
so no unstripped rebuild is needed:

1. String-literal anchoring of stripped frames: `0x67ac9c` owns
   `running borrow check` / `borrow check skipped (--no-borrow-check)` →
   `CompilerDriver.borrow_check()` (`driver_pipeline_passes.spl:10-19`);
   `0x66b368` sits between the `aot:borrow_check:start` / `:done` literals
   (`driver_aot_pipeline.spl:97-102`); `0x5183ae` → `check_mir_module`
   (`borrow/borrow_check/mod.spl:405`).
2. `SIMPLE_COMPILER_TRACE=1` (gate at `driver_log_helpers.spl:20`) — last line
   before death is
   `[BOOTSTRAP-PHASE] +512ms aot:borrow_check:start heap_registry=3545`.

Fault shape: PC `0x5178e6`, `mov 0x8(%rax),%r14` reading a list length word,
`SEGV_MAPERR si_addr=0x118`. The value at field +0x58 is `0x111` — a tag-1
value whose pointer part `0x110` is below the first mapped page. The runtime
helper at `0x6a178b` correctly *refuses* it and returns it verbatim; the caller
then masks with `and $~7`, rejects only `0..7`, and dereferences.

### Three traps when working this crash

- **`--no-borrow-check` does not bypass it.** Same PC, same trace,
  `aot:borrow_check:start` still emitted. The flag is not honoured on the
  `compile` path — do not assume you can route around this layer.
- **`SIMPLE_BOOTSTRAP=1` does skip it** (`bootstrap_flat_aot`), which exposes a
  *different* fault at PC `0x4942cd` in MIR lowering. Do not conflate the two.
- **`Dict.len()` returns -1 in this artifact** (`functions=-1` from
  `driver_pipeline_lowering.spl:229`), one statement upstream of the
  `module.functions.keys()` loop that crashes. Adjacency is recorded; causality
  is not established.

Not LIM-010 (SIGABRT-shaped), not the 2026-07-09 LLVM ICMP bug (downstream of
this layer), not the 2026-08-01 placeholder-nil bug (SIGILL, pre-HIR).

Detail: `doc/08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`.
Tracked: `.spipe/stage3-segfault-fix/` AC-3, AC-4.
