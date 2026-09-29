# Match pipe alternative consumed as bitwise OR

Status: open; separate from the case-prefixed fat-arrow correction.

## Observed failure

Source d405819f00df98f51320631f8001550ba5852e89, bootstrap-only source-built
parser component produced by seed82ee7562, failed assertion21:

```simple
fn f(n: i64) -> i64:
    match n:
        case 0 | 1 if n >= 0 => return 10
        case 2 => return 20
```

Parsing reported no error, but `arms.len() == 3` failed. The first four separate
fat-arrow cases had passed; the other cases had not run. Retained evidence:
`/mnt/simple-bootstrap-6b2/case-arrow-focused-d405-cycle1-20260929/component-run.log`.
The observed output does not print the actual arm count; it proves inequality
with the expected three, not a measured count of two.

## Causal source evidence

`parser_stmts.parse_match_arms_common` calls general `parse_expr` for the first
pattern before its TOK_PIPE/TOK_COMMA alternative loop. `TOK_PIPE` is121 and
`parser_expr.parse_multiplication` consumes121 into `expr_binary`, so the pattern
separator is already consumed before the alternative loop can recognize it.
This code predates the fat-arrow separator/body fix.

## Scope and pending acceptance

The fat-arrow guard regression uses existing comma-separated alternatives to
isolate that fix. This does not fix or qualify pipe-separated alternatives.
A separate parser correction must preserve ordinary bitwise OR expressions,
create one arm per alternative with the shared guard/body, and verify the exact
source above plus nested patterns. No pipe-fix test PASS is claimed.
