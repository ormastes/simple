# Text-session codec configuration scenarios

Authored manual for `test/02_integration/io/text_session_codec_spec.spl`; **UNRUN**, not a generated PASS report.

1. Select UTF16LE/Require input and UTF16BE/Forbid output with different byte limits. Read all eight getters and compare the exact requested values.
2. Select the explicit UTF8 compatibility factory; observe UTF8/NotApplicable/Preserve both ways. No locale is consulted.
3. Reject unknown input and output labels with nested CodecError.UnknownEncoding at -1; reject inconsistent input/output byte order with InvalidFormat at -1.
4. Reject zero, negative and above-16-MiB limits independently on both sides with the corresponding actionable Io diagnostic. Accept exactly 1 and 16777216 and preserve both getters.
5. Keep two profiles independent; selecting a second codec must not change the first.
6. Call public validate on admitted profiles. A required BOM is accepted as configuration metadata without a payload; stream owners must enforce it later.

The ten real cases preserve the reviewed six-case donor suite and add missing boundary/public-validation cases. They do not open resources, test I/O byte enforcement, or establish compiler privacy, runtime memory safety or allocation behavior. See `doc/05_design/sosix_text_sessions_20261019.md` for remaining provider/OOM/performance gates.
