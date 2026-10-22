# Checked stdin session specification

Authored companion, not generated execution evidence. All 17 scenarios UNRUN.

Actual suite: `test/02_integration/io/sosix_stdin_session_spec.spl`.
Native fixture: `test/fixtures/native_sosix_stdin_session/main.spl`.
Explicit absolute `SIMPLE_STDIN_SESSION_FIXTURE` is required; the existing bounded
process provider pipes precise octal bytes to fd0 and asserts exit 0, the exact
success line and empty stderr. No runner or compiler has been launched.

1. preserves UTF8 NUL and split supplementary scalar.
2. decodes UTF16LE BOM and surrogate pair.
3. decodes UTF16BE BOM and surrogate pair.
4. preserves a requested BOM as scalar text.
5. rejects forbidden BOM without consuming the following scalar.
6. reports missing UTF16 BOM.
7. sticks to malformed UTF8 error without another read.
8. rejects truncated UTF8 only when EOF is observed.
9. rejects truncated UTF16 at EOF.
10. rejects invalid read sizes before IO and never closes borrowed stdin.
11. distinguishes empty EOF from an incomplete scalar.
12. rejects unknown formats and invalid limits before consuming input.
13. decodes UTF32LE with immutable BOM and endian policy.
14. decodes UTF32BE with immutable BOM and endian policy.
15. preserves a typed sticky provider failure for closed fd0.
16. shares logical close across ordinary class references.
17. cancels pending input without finishing or closing the descriptor.

See `doc/05_design/sosix_stdin_text_session.md` for ownership, bounds and open qualifications.
