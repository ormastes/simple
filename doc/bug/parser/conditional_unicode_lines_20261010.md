# Conditional preprocessing must preserve UTF-8 source bytes

The old line splitter mixes text iteration, length and indexing while copying every character through an array. Imported @cfg source with an em-dash comment failed HIR prepass under pure producer f5ee while the identical ASCII control emitted an object. Six full-CLI files failed near EOF; the byte/scalar difference matched each truncated tail. This correlation does not establish a causal stack.

Replace the splitter with the existing newline split operation. Seven real source-hosted owner tests pass: empty input, trailing/consecutive empty lines, CRLF, Unicode comments and literals, final source bytes and embedded NUL. Windows runtime split uses explicit byte lengths and retains trailing fields.

Native integrated validation is pending. The pure producer used for the original failing pair does not contain this patch. Broad compiler/lib/MCP/LSP verification remains blocked by the current bootstrap tool capability and full-CLI parse defects. No whole-build speedup is claimed.
