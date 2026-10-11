# Phase 1 orphan compatibility notes

Twenty release specs contain bare Markdown compatibility prose followed by a
closing triple quote, with no preceding opening triple quote. The interpreter
therefore parses words such as `on` as language syntax, or consumes subsequent
test source as a string. This blocks their original assertions before execution.

Convert only the exact malformed note to comments, preserving line count,
imports, scenario bodies, and assertions. Also comment the adjacent bare
operator instructions in manual_mode_spec and correct their historical path.
No implementation or test oracle changes.

There are 131 specs containing this compatibility sentence. Only the 20 exact
orphan shapes with no preceding triple quote are edited. The 102 files with
earlier docstrings and nine other shapes are left for separate review; sentence
presence alone does not establish a bug.

Evidence: build/phase1-full-backlog-20261011 contains the selection, before/after
hashes, reversible exact transformation checks, and notes-probe-receipts.json.
The full unmodified sdoctest source at release df95ec0112ddbc0070d83b1d4a1070b7434aff83
fails before execution with expected pointcut expression, found `the`.
The comment repair executes all 49 original examples: 49 passed, zero failed,
skipped, or dropped. Cached producer SHA256:
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.

This is a bootstrap diagnostic for source repair, not admitted pure runtime,
native, or all-20-spec execution qualification. Other pre-existing malformed
fixture scopes, missing imports, platform assumptions, and stale assertions
remain possible. No green criterion replay or compiler rebuild occurred.

The original 4,758-row queue is unchanged. The full path/outcome listing is
build/phase1-component-backlog-20261011/ALL_4758_TEST_RUNS.csv. Historical
reconciliation finds 3,502 invocations reporting failed cases and 1,256 with
other unresolved outcomes. This repair does not claim all backlog entries fixed.
