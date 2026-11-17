# Borrow check "ownership CFG work budget exhausted" on the Stage 3 self-build (2026-11-17)

Symptom: the r18 Stage 3 compiler, compiling the compiler's own sources,
failed borrow check on two functions with
`ownership CFG work budget exhausted`:
`MirLowering.lower_expr_impl` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`)
and `MirLowering.lower_enum_match_flat`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`). Those two
failures blocked the other 1360 modules in the MIR shard pool.

Root cause, in `OwnershipFlow.check`
(`src/compiler/55.borrow/borrow_check/ownership_flow.spl`):

1. Solve order. The fixed point used a FIFO queue. In an if-chain or a match
   whose arms each move something, every arm reaches the join one queue round
   later than the one before it, so the join and every block below it ran
   again once per arm, each time with a larger maybe-moved set.
2. Join cost. Each edge rebuilt the target's set with a linear `contains` per
   element, including the first edge into a block, where nothing can be a
   duplicate.
3. Budget. `NLLChecker.check` (`nll.spl`) called the solver without a budget,
   so the fixed default of 1,000,000 applied to every function whatever its
   size.

Fix:

- Blocks are solved in reverse postorder sweeps over dirty blocks. A join runs
  after its forward predecessors, so an acyclic region converges in one sweep
  and a loop nest in about one sweep per nesting level.
- The first edge into a block shares the source state. Later edges skip the
  prefix the two states have in common and copy the target's set only when
  something is added.
- `OwnershipFlow.work_budget` scales the budget with the function:
  `16 * (blocks + points + edges + events) * (1 + moves)`, never below the
  former 1,000,000 and never above 2,000,000,000. `NLLChecker.check` passes
  it. The budget is still fail-closed. An explicit `work_limit` behaves as
  before.
- The transfer function (`ownership_event_transfer`), the join (set union) and
  the replay that reports diagnostics are unchanged. Diagnostics keep
  breadth-first block order; that walk now runs only when there is an error.

Evidence (Rust seed built 2026-11-17 19:11 from `b0bc26617cf3`, sha256
`fba00c37a4bc7195…`; shared host, so wall times are noisy):

- `test/01_unit/compiler/borrow/ownership_flow_spec.spl`: before, 15 of 20
  (the five new large-function examples fail); after, 20 of 20.
- Differential probe, 400 pseudo-random CFGs with loops, unreachable blocks
  and Move/Read/Revive/Write events on whole locals and fields, 671
  diagnostics: output byte-identical before and after.
- 120-arm if-chain with a 120-block tail under a 4e9 budget: before 4.4 s and
  2.3 GB RSS; after 0.5 to 1.5 s and 50 MB.
- 20,000 checks of an 8-block function (diamond inside a loop): user CPU
  1.15 s before, 1.38 s after the first landing (#10023), including probe
  setup. See the follow-up below.

Follow-up, small functions (same seed, interleaved runs): the reverse
postorder walk cost about 11 microseconds per function, more than it saves
when the function is small. Functions of at most 32 blocks now skip the walk
and use a FIFO queue; its repeated visits below a join are bounded by that
size. The queue's visit order is the diagnostic order, so that path needs no
second walk either. Mean user CPU over six interleaved runs of the 20,000-check
probe: 1.25 s before any change, 1.48 s after #10023, 1.23 s now (RSS 384,
455 and 393 MB). The 120-arm chain stays at 0.1 s user and 46 MB. The 400-CFG
probe and a second one over 150 CFGs of 33 to 62 blocks (571 diagnostics) are
byte-identical to the pre-fix solver. Still slower than before: a 15-block
function that reports an error, 0.50 s to 0.55 s mean over 2,666 checks.

Not verified: the two real functions. That needs a Stage 2 and Stage 3
rebuild; the seed cannot borrow check those files through the pure-Simple
pipeline at a usable cost.

Left as is: `src/verification/ownership_flow/source_bindings.sdn` records a
hash of the `OwnershipFlow` declaration from 2026-11-07. This change edits
that declaration, so the recorded hash is historical. The other bound
declarations in the file are byte-identical and on the same lines.
