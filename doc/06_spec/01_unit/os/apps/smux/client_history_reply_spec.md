# SMUX interactive history reply budget

**Status: authored manual; execution and docgen pending (TEST_BLOCKED).**
Source: `test/01_unit/os/apps/smux/client_history_reply_spec.spl`.
Requirement: **REQ-SMUX-INTERACTIVE-005**, traced in all eight unexecuted cases.

The production `client_history_reply(prefix, content, limit=65536)` helper
budgets the complete response body, including its header and newline. It keeps
the newest whole text lines; no line or UTF-8 scalar is byte-sliced. A newest
line that cannot fit returns a typed error. Public history capture retains its
separate explicit-limit failure contract.

1. Build 2000 ASCII rows of exactly 80 columns. The reply stays at or below
   65536 encoded bytes, includes the newest row, excludes the oldest and retains
   an exact contiguous suffix of source rows.
2. Build 2000 wide-Unicode rows with different earlier/later lengths. Count
   encoded bytes rather than scalar or cell counts. Every retained row equals
   its complete known-valid source row, including the newest row; older rows
   are trimmed and no partial Unicode encoding is introduced.
3. Keep a fitting history snapshot exactly, including CJK, emoji and a
   decomposed combining mark.
4. Count prefix and separator bytes in exact-fit cases.
5. Refuse an oversized newest line instead of slicing its UTF-8 bytes.
6. Return a header-only empty history when its prefix fits; refuse oversized
   prefixes and negative budgets.
7. Preserve a fitting trailing newline without adding unbudgeted separators.
8. Inspect at most the newest 2000 candidate lines, matching the interactive
   caller's source-row limit. Earlier rows beyond that finite window are omitted.

The upstream interactive caller must also bound history retrieval to 2000 rows;
this helper's candidate loop is finite but splitting supplied text still depends
on the supplied content size. The tests call the production pure helper; they
prove no history capture, network framing, clipboard or live copy-mode behavior.

After qualified runtime admission, execute this spec, generate its mirrored
manual with zero stubs and run `sspec-maintain scan`, preserving runtime identity,
executed case counts, exit status and artifacts. None of those gates has run.
