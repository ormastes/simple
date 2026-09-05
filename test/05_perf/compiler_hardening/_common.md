Each bench file is standalone on purpose: one unsupported operation demotes the
WHOLE program to the interpreter (.claude/rules/testing.md), so mixing a
fn-pointer bench with an enum-match bench would silently measure the same engine
for both. Every file prints exactly one line: `BENCH <name> <ns_per_op>`.
