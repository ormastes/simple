# Array range tail index execution gap

Status: open; pre-existing before open-range endpoint repair.

`[10,20,30][1..]` parses as EXPR_INDEX over EXPR_RANGE. The G43 parser comment names this grammar, but does not establish runtime slicing support. Both the original parser and repaired parser reject it in the seed-hosted evaluator with `type error: array index must be int, got array`; both also reject `[10,20,30][1..(-1)]`. The repaired parser correctly distinguishes absent versus authored endpoint in flat and tree AST.

Pure owner evidence: core/interpreter/eval_access.spl eval_index_expr evaluates index as an ordinary expression and accepts only integer array indexes. MIR _MirLoweringExpr/expr_dispatch.spl lower_index explicitly rejects array Range indexes; its text-range helper is separate. EXPR_SLICE colon syntax is a distinct representation and is unchanged by the Range endpoint repair.

Required follow-up: implement genuine range-index slicing semantics at the array owner, preserving absent bounds and authored negative endpoint rules consistently across interpreter and native MIR. Do not materialize an unbounded range to obtain array slicing. Pin array-tail output and authored negative semantics before claiming runtime support.

Evidence: /tmp/simple-open-range-parser-evidence/slice-before.log and slice-after.log. Bootstrap seed SHA256 57aeb8786f2a767b2052672b988b6bcfcabff2a3033594e97606ceabc7ebb3ce. No Phase2/native slice PASS claimed.
