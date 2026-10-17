# Async HTTP header wire grammar

Requirement: REQ-LIB-NOGC-ASYNC-MUT-001.

Executable specification: `test/01_unit/lib/nogc_async_mut/http_server/async_header_lexical_contract_spec.spl`.

These scenarios exercise the production `HttpRequestParser`, without a stub parser.

| Scenario | Expected behavior |
| --- | --- |
| Whitespace before the colon | Reject SP/HTAB before the colon and store no header. |
| Separators and non-ASCII names | Reject HTTP separator punctuation and Unicode names. |
| Valid token punctuation | Preserve every allowed tchar punctuation character. |
| Control bytes in names | Reject all ASCII C0 controls and DEL. |
| Control bytes in values | Reject every C0 control except HTAB, including at either edge before trimming; reject DEL. |
| Legal field values | Preserve interior HTAB and Unicode text; trim surrounding whitespace. |
| Fragmented malformed header | Report the lexical diagnostic, enter Error and remain incomplete after further input. |
| Malformed framing | Retain the missing-colon and empty-name error. |

Status: AUTHORED_UNEXECUTED (2026-10-16). No qualified self-hosted full CLI was available in this validation lane. Source review and whitespace checks do not establish runtime correctness.

A separate native fixture using the production parser reached HIR 21/21 with
21 cache hits under the retained A174 pure-Simple compiler. The final frozen
attempt was resource-aborted: peak process-tree RSS 4,195,404 KiB exceeded the
4,194,304 KiB limit; guard exit 88, `quiescent=1`. Source checksums matched
before and after. No executable or native case summary was produced. This
establishes that this diagnostic budget was insufficient for that producer;
it does not establish a parser behavior failure or a SSpec PASS.

The draft remains unfinished pending actual native and SSpec execution, the
mandatory compiler/core/MCP checks and canonical bug-DB reconciliation.
Detailed reproduction and evidence paths:
`doc/08_tracking/bug/async_header_native_qualification_rss_2026-10-16.md`.

The broader tracked bug also covers Host presence, authority validation and absolute-form target agreement. These scenarios do not claim those requirements are repaired.
