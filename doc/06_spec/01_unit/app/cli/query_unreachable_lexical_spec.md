# Query UNREACH001 Lexical Successor Specification

UNREACH001 recognizes `return` only at the first executable token of a line and
selects the first later executable line at the same or shallower indentation.
Blank lines, comments, and string payload never become return origins.
Standalone ordinary/triple string literals remain executable successor tokens;
only triple-string interior and closing-only lines are excluded.

The executable fixture proves that a comment-only tail before dedent emits no
warning, a docstring containing return/call text emits no warning, and a real
same-indent statement after an intervening comment produces exactly one JSON
diagnostic at line 4, columns 5–9. Direct index assertions pin lexical return
flags, zero code columns for triple-string lines, successor identity, and token
end columns. Source contracts require both live lint emission and collected
query-check JSON to consume the shared fields.
Additional cases report standalone ordinary/triple literals at their opening
quote and prove a final string expression keeps a preceding call non-final for
RET001.

The index performs one stateful lexical scan plus one reverse monotonic-stack
pass: O(N+L) time for N source bytes and L lines, with O(L) scalar facts and
stack storage. It does not allocate a masked source copy and does not scan a
suffix per return. RET001 reuses the same executable-line last-statement facts.

No tests, compiler, lint command, timing, allocation, or RSS execution was
performed under the user override.
