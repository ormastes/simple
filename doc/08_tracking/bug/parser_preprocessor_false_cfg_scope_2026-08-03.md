# False `@cfg` declaration scope skipped comment bodies and crossed indentation

Status: fixed in the isolated `codex/stage4-x86-phase4` lane; pending exact x86 Phase 4 verification.

The text-level `@cfg` preprocessor must preserve source-line count while removing
an inactive declaration. Its former false-declaration traversal treated a blank
line as a declaration-body boundary and consumed the next non-preamble line even
when that line belonged to a different indentation scope.

The repair keeps skipping across blank and comment-only body lines, walks a
same-indent decorator stack, and only removes a declaration at the `@cfg` line's
indentation. Focused source tests cover comment-only body lines, indentation
boundaries, blank docstring paragraphs, nested `@cfg`, and normal decorators.

Known follow-up (not part of this repair): inactive declarations with multi-line
function signatures need header parenthesis-depth tracking before body-dedent
skipping begins. This remains explicitly outside the isolated fix.
