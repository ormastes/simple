# Iso Ownership Feature Expert

## Role

Own feature-specific process knowledge for `Isolated` (`iso`) ownership
transfer and its borrow-check enforcement — the move/use-after-move detection
system for `iso`-typed values across the pipeline (parse → HIR → MIR → borrow
check). Tracks which transfer sites emit real Move instructions, which
detection gaps have been closed, and what's still open.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/IMPL.md)

## Feature Links

- Move emission (HIR→MIR): [layer_expert/mir_lowering/skill.md](../../layer_expert/mir_lowering/skill.md#iso-ownership-emit_move-had-exactly-one-caller-before-6a53442f-2026-08-06)
  — `MirBuilder.emit_move` at [src/compiler/50.mir/mir_data.spl:353](../../../../src/compiler/50.mir/mir_data.spl).
- Use-after-move detection: [layer_expert/borrow_check/skill.md](../../layer_expert/borrow_check/skill.md)
  — `src/compiler/55.borrow/borrow_check/`.
- Isolated-type predicate: `mir_hir_type_is_isolated` at
  [src/compiler/50.mir/mir_lowering_stmts.spl:48](../../../../src/compiler/50.mir/mir_lowering_stmts.spl).
- Tracking: [doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md](../../../08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md).
- Specs: `test/01_unit/compiler/borrow/` — `borrow_check_spec.spl` (11/11),
  `iso_move_pipeline_spec.spl` (3/3), `iso_move_sites_spec.spl` (2/2),
  `iso_move_assign_field_spec.spl` (8/8), `iso_use_after_move_e2e_spec.spl`
  (4/4, real source text end-to-end), `iso_parse_pipeline_spec.spl` (3/3).

## Status (2026-08-06 — `63dc29b1` detection, `6a53442f` emission)

**What landed:**

- **Move emission** now covers six transfer sites (up from one before
  `6a53442f`): let-binding (`val b = a`, pre-existing), call argument,
  reassignment (`b = a`), field store (`o.f = a`), array element store
  (`arr[i] = a`), dict element store (`d[k] = a`). Array/dict stores are the
  non-obvious case — they lower to `rt_array_set`/`rt_dict_set` runtime
  CALLS, not Store instructions, so a synthetic `emit_move` into a fresh
  local is inserted ahead of the call. All sites keep the guard: only a PLACE
  read of an existing binding moves, never a fresh construction; only the
  plain (non-compound) assignment form.
- **Use-after-move detection** now covers call arguments (previously silent
  — args ride as bare operands, no separate Copy/Move instruction existed to
  hang a use-fact on) and terminators (`return x` after a move — the walker
  previously never visited the block terminator at all). "Move-then-use is
  undetectable" is a STALE claim; SF1 (2026-07-28) added forward
  propagation via `moved_now`.
- Emission and detection are proven independent: disabling either alone
  re-breaks only its own spec case, not the other's.

**Still open:**

- No Move emitted ahead of `Ret` (lowering side — the checker can now see a
  terminator use, but nothing marks the returned value moved-out first).
- `list.push(x)` has the same missing-Move gap as the pre-fix call-argument
  case, at `_MirLoweringExpr/method_calls_literals.spl:874`.
- Both tracked in `doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`.

**Deliberately not fixed (unreachable, not a bug):**

- Iso **struct**-field binding TODO at `mir_lowering_stmts.spl:664-672` is
  UNREACHABLE by construction — `find_local_hir_type(x) == Isolated` and
  `struct_value_syms.get(x) != nil` can never both be true, because
  `_MirLowering/function_lowering.spl:206` and `:239` match
  mutually-exclusive variants of the same `param.type_.kind`. An agent
  implemented it, measured no spec change, and correctly reverted rather
  than ship dead code. Unblock condition: `:239` must unwrap `Isolated`
  before its `Named` check — do that first if this TODO is ever picked up
  again.

**Does not reach users yet:** `bin/simple` is the Rust seed
(`src/compiler_rust/`), which has zero borrow-check code. Stage-3 self-host
is blocked (see `.claude/rules/bootstrap.md` and
`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`).
That blocker outranks further iso-ownership work — everything above is
exercised only via `bin/simple test`'s interpreter path over
`src/compiler/**` source, not by any deployed binary.

## Implementation Constraints

- Compiler `.spl` source under `src/compiler/**` is live under `bin/simple
  test` (no bootstrap rebuild to iterate) — but that's the interpreter path
  only; it says nothing about JIT/native or `bin/simple run` (seed).
- Verify with `timeout 900 bin/simple test <spec> --no-cache --no-cover-check`
  and grep the `^Results:` verdict line — output is flooded with lint/gc
  warnings that read as "no tests ran" if you don't anchor on that line.
- Sabotage-probe every change (break → RED, revert → GREEN) before trusting a
  spec result.

## Update Rule

When new `iso` transfer sites gain Move emission, when detection gains new
use-fact sources, or when the stage-3 self-host blocker clears (making this
reachable from `bin/simple`), update this skill and its two linked layer
experts (`mir_lowering`, `borrow_check`) together.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
