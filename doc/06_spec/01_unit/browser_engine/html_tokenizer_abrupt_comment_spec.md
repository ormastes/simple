# Abrupt Empty HTML Comment Specification

This focused scenario verifies the WHATWG recovery boundary for abrupt empty
comments. It does not claim full HTML comment-state conformance.

## Emit empty comments and resume after both abrupt closers

1. Tokenize `<!--><p>x</p>` and `<!---><p>y</p>`.
2. Verify each stream contains an empty Comment, paragraph StartTag, visible
   Character, paragraph EndTag, and EOF in that exact order.

## Keep non-closing controls open through EOF

1. Tokenize `<!--!><p>x</p>` and `<!--abc<p>y</p>`.
2. Verify each stream contains only its complete remaining comment data and
   EOF; no paragraph token escapes the comment.

## Count abrupt comments within the retained-token quota

1. Apply a one-token quota to an abrupt comment followed by a paragraph and to
   one unterminated comment.
2. Verify the abrupt stream retains Comment plus the conventional out-of-quota
   EOF and reports truncation when the paragraph exceeds the quota.
3. Verify the unterminated stream retains Comment plus EOF without reporting
   truncation.

## Preserve an abrupt-comment suffix through every render phase

1. Compare the target element's semantic attribute between the control page
   and pages prefixed by `<!-->` and `<!--->`.
2. Compare the target's computed x, y, width, and height.
3. Compare its canonical Draw IR kind, identity, geometry, and color.
4. Compare the complete final pixel buffers.

All comparisons use direct built-in SSpec matchers. The executable source is
`test/01_unit/browser_engine/html_tokenizer_abrupt_comment_spec.spl`.
