# Phase1 inline assignment followed by block elif loses else

An inline indexed assignment followed by an indented elif body and a final else failed with UnexpectedElse. This valid grammar appears in the bootstrap admission inventory path.

The statement-if helper constructed an elif node from its block and returned without consuming subsequent branches. A shared block-finishing helper now consumes the remaining chain for both inline and block elif bodies. It preserves the following sibling statement.

Validation: two new AST regressions passed, covering a nested conditional expression and multiple block elif branches. The remaining 47 control-flow regressions were run separately without rerunning the two new green tests. See /home/ormastes/simple-linux-rc1-20261005/mixed-parser-evidence/.

This repairs the bootstrap Rust seed parser only. Whole Phase1 and subsequent pure-Simple generations remain unqualified.
