# LSP document sync fails to reject changes on unopened documents

**Date:** 2026-11-12  
**Status:** verification-pending  
**Category:** LSP / Document Sync

## Symptom
Test case "rejects changes without an open owner and malformed notification JSON" in `test/01_unit/app/lsp/document_sync_spec.spl` fails on Windows (14/15 passing).

The test expects:
```spl
lsp_document_sync_apply("textDocument/didChange", sync_change(uri, 1, [sync_text("text")]))
```

to return `false` when the document has never been opened, but it appears to be returning `true`.

## Analysis
- `lsp_document_sync_apply()` in `src/lib/nogc_sync_mut/lsp/lsp_document_sync.spl` calls `LSP_DOCUMENT_OWNER.update_doc()` on line 82
- `update_doc()` in `src/lib/nogc_sync_mut/lsp/server.spl` line 127 correctly returns false if document not found: `if idx < 0: return false`
- Expected behavior: didChange on unopened document should reject at the sync adapter level

## Reproduction
```bash
cd test/01_unit/app/lsp
../../bin/simple test document_sync_spec.spl
# Look for the single failing case in "rejects changes without an open owner and malformed notification JSON"
```

## Hypothesis
Either:
1. The JSON parsing/extraction in `lsp_document_sync_apply` is succeeding when it should fail
2. The implicit return at end of `lsp_document_sync_apply` (line 82) is not being executed
3. There's a scoping issue where `LSP_DOCUMENT_OWNER` doesn't properly reject unopened documents

## Next Steps
- Run test on Windows to identify exact failure point
- Add debug assertions to trace execution path
- If product is correct, the spec expectation may need adjustment

**Files affected:**
- `src/lib/nogc_sync_mut/lsp/lsp_document_sync.spl` (line 82 - implicit return)
- `src/lib/nogc_sync_mut/lsp/server.spl` (line 124-143 - update_doc implementation)
- `test/01_unit/app/lsp/document_sync_spec.spl` (line 101-106 - test case)

## Resolution (2026-11-12)
Root cause was in the spec, not the product. The failing expectation was the
second one: `"{invalid}"` is an interpolated string literal, so evaluating it
raised `semantic: variable \`invalid\` not found` and failed the example before
`lsp_document_sync_apply` ran. The unopened `didChange` already returned
`false` (`update_doc` -> `find_doc < 0`). Fix: use the raw literal
`r"{invalid}"` so the adapter receives malformed JSON as intended.
Before: `executed=15 passed=14 failed=1`; after: `executed=15 passed=15 failed=0`.
