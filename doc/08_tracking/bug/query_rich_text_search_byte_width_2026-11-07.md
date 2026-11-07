# Rich-query needle width must remain byte-based

Source finding, not executed reproduction. Runtime NOT_RUN. Selected design
#7425 makes text.len count code points while substring/byte_at remain byte APIs.

At release 96499dfa782, `_find_in_line` and `_find_in_line_from` use len for
receiver bounds and needle widths. With character-count len, `A한éZé` / `é`
uses one byte for a two-byte needle, and empty-needle acceptance stops before
the byte end. The existing sentinels are 0 / -1; they are intentionally retained.

Fix: use exported `std.common.string_core.str_len` for both text operands,
cache byte counts once, preserve the original search/comparison algorithms.
Real-owner reproduction/prevention and manual:
- test/01_unit/app/cli/query_rich_byte_search_spec.spl
- doc/06_spec/01_unit/app/cli/query_rich_byte_search_spec.md

## Pending migration overlap

Other-owner #7429 head796187cbb6e changes `_find_in_line`'s line.len to
line.byte_len but leaves pattern.len in the bound and cut; it changes all three
_find_in_line_from length uses to byte_len. This narrow change intentionally
uses the already exported byte owner for both functions. When integrating
#7429, retain these coherent byte widths; do not restore pattern.len or apply
the old partial hunk blindly. No other migration hunks are copied. #7436 stays
draft and its semantic flip is not authorized by this fix. Native qualification
and the wider cross-receiver migration remain separate OPEN work.

Source-review cycle 2 corrects NUL fixture construction: production bytes_to_text
creates explicit length-bearing carriers and needles, with byte-length/content
assertions before invoking the search owner. Raw NUL literal promotion is not
used as evidence for search correctness. Product source is unchanged by this
fixture correction. Runtime remains NOT_RUN.
