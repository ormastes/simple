# Formatted-string lexer allocation amplification
**Status:** OPEN (unverified 2026-09-12)

Lexing 16,384 multilingual formatted strings currently performs 458,769
allocations (~28/string), allocates 62,143,720 bytes cumulatively (~3.8
KiB/string), retains 31,735,808 bytes in live tokens, and peaks at 43,738,698
bytes above the source fixture.

Replace cloned lexer/backtracking state and owned literal/expression/format
segments with compact byte checkpoints and borrowed source ranges. Allocate
only transformed escapes and finalized owner-bound AST/interned values.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and has no cheap repro reachable within budget; left open with an explicit unverified status line.
