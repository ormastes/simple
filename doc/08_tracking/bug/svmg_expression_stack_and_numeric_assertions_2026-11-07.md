# SVM-G expression stack balance and numeric assertion representation

Date: 2026-11-07
Status: source repair reviewed; runtime verification pending

## Failures

- Consumed `If` and `IfChain` expressions discarded their tail values before
  the consuming assignment or arithmetic operation. Missing branch tails or
  an absent else branch could also leave the consumer without a value.
- Ignored scalar expressions and helper-call results in branch statements
  remained on the operand stack. A local initializer could then use an ignored
  value as its store address; repeated loop iterations could overflow the
  reference VM's 256-word stack.
- Discarded block tails emitted `DROP` after `print` or `For`, although those
  expressions leave no operand word. A consumed conditional also accepted a
  present tail containing `print` or a loop without a value.
- `expect(actual).to_equal(expected)` selected `FEQ` when either operand was
  floating. Integer `1065353216` could therefore compare equal to float `1.0`
  because their raw words coincide. The symmetric operand order was affected.

## Repair and regression coverage

`src/compiler/70.backend/svmg_lowering.spl` preserves conditional tails in
value context and requires a tail value on every branch, including else.
Expression statements and discarded block tails share one dispatcher: scalar
and helper results are dropped, while print, loops and assertions retain their
zero-word contract. Consumed conditional tails reject known zero-word forms.
Numeric assertions reject mixed integer/float representations before comparing.

`test/01_unit/compiler/backend/svmg_lowering_spec.spl` covers conditional values,
both selected legacy branches, each flat-chain path, ignored helper results
with observable side effects, sentinel locals, 300-iteration for/while loops,
zero-word statement tails, rejected zero-word/missing conditional tails and
missing else branches. Numeric cases cover both mixed operand orders, Bool
results of float comparisons, and preserved float signed-zero equality.

## Evidence and remaining verification

An independent Astra source review found no remaining P0/P1 findings in the
repair delta. Static delimiter and whitespace checks passed. These checks do
not establish executable correctness.

No usable self-hosted compiler runtime was available in this worktree. The
regressions were authored but **not executed**; compiler/core/MCP verification
also remains pending. No Rust-seed fallback or runtime PASS is claimed. Run
the scoped SVM-G lowering spec and required compiler/core checks with an
admitted self-hosted runtime before treating this repair as runtime verified.

This report supplements existing historical SVM-G reports without changing
their recorded evidence or status.
