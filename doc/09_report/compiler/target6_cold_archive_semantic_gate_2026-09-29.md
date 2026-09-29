# Target 6: semantic archive gate before index publication (2026-09-29)

The cold publisher already verified the persisted archive digest, exact
three-member layout, member digests, UTF-8, and manifest binding. It now also
uses the warm route's symbol/action payload parsers before moving the package
index `CURRENT` pointer. The shared parser rejects malformed symbols or
actions and actions whose target symbol is absent. The warm decoder consumes
the same parsed result, so the two boundaries apply one semantic rule.

No-stub Stage-2 native build of
`test/02_integration/compiler/cache/cold_hir_compact_output_index_spec.spl`:
336 compiled, 0 failed. Native execution: 7 examples, 0 failures. The added
case persisted a digest-valid archive with invalid interface text and proved
that publication failed while the index pointer stayed absent. This is a
focused diagnostic linked against a hosted runtime archive, not a Stage-4
production or memory/performance qualification.

A pinned-reader replacement was tested and reverted after a 542-byte archive
caused a Stage-2 worker to reach 15,864,992 KiB RSS at nearly full CPU. See
`doc/08_tracking/bug/target6_stage2_pinned_archive_read_rss_runaway_2026-09-29.md`.
The current bounded verifier keeps its existing memory behavior; this change
adds semantic validation work on cold publication and makes no time/RSS
improvement claim.

Real compiled archive output generation, production V3 graph publication,
full CLI cutover, and paired warm/cold time-RSS gates remain open.
