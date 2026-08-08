# Query/LSP W0404 configuration false green

## Symptom

`@allow(visibility_boundary)` and `@deny(visibility_boundary)` did not affect
the Query/LSP wide-public diagnostic W0404, although the public lint CLI did.

## Root cause and fix

`query_lint._governed_lint_codes()` omitted W0404, so it never received the
shared severity override. Add W0404 to that shared list and cover allow/deny
through the existing query/LSP severity oracle.
