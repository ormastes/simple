# Smux typed-key byte codec

REQ-CMUX-003/006/008. **AUTHORED / NOT_RUN v2: 19 unit scenarios, zero executed.** This is a manual mirror of `test/01_unit/os/apps/smux/core_mux_key_codec_spec.spl`; canonical docgen and SSpec maintenance are NOT_RUN.

Each scenario calls production `core_mux_keys_bytes_v1`, directly or through `key_codec_bytes` / `key_codec_error`. Expected bytes are independent literals. These are pure codec controls, not PTY effects, application behavior, backend parity, or full CoreMux admission.

| Scenario | Production oracle |
|---|---|
| Temporary allocation mismatch | Production `core_mux_key_bytes_checked_v1` rejects empty, shortened, oversized and invalid expected-length carriers with Unavailable/NotApplied. This is deterministic admission testing, not an induced OOM. |
| Exact temporary allocation | The same production seam preserves all admitted 1–7-byte lengths, NUL bytes and explicit cursor bytes. |
| Fixed Named keys | Enter, Escape, Tab, Backspace, Delete, PageUp and PageDown preserve exact bytes in both cursor modes. |
| Normal cursor keys | Up/Down/Right/Left/Home/End emit exact CSI sequences. |
| Application cursor keys | The same six keys emit exact SS3 sequences from the passed mode boolean. |
| F1–12 | All twelve xterm base capability strings match independent arrays. |
| F13–24 | All twelve shifted xterm capabilities match independent arrays. |
| Unicode boundaries | NUL, DEL, every UTF8 width boundary, surrogate neighbors, and U+10FFFF have exact bytes. |
| Control ranges | Upper/lower letters and punctuation range edges have exact C0 results. |
| Control aliases | Space, 2–8, slash, hyphen and question mark have explicit expected mappings. |
| Eight ASCII modifier combinations | A, Alt-A, Ctrl-A and Alt-Ctrl-A encode; all four Shift-A forms return Unsupported. |
| Eight Unicode modifier combinations | Emoji and Alt-emoji encode; the six Control/Shift forms return Unsupported. |
| Eight Tab modifier combinations | Tab/Alt-Tab/BackTab/Alt-BackTab encode; all Control-Tab forms reject. |
| Unsupported control and layout cases | Legacy unchanged-Control cases and guessed Shift-2/Shift-Enter transformations reject. |
| Invalid Unicode | Both surrogate edges and above-range values reject under all eight modifier combinations. |
| Function/count limits | F0/F25/extreme function indices, empty input and 257 keys reject; 256 keys encode. |
| Whole-request capacity | Alt prefix and F24 fit exactly at nine bytes; insufficient/invalid budgets return InvalidRequest. |
| Invalid/unsupported suffix | A good prefix followed by a bad key returns only a typed error; later independent valid calls remain exact. |
| Mixed ordering/max payload | Mixed Named/NUL/Alt-Control bytes retain order; 256 F24 keys fit 1792 bytes and refuse 1791. |

Every negative helper asserts the exact error kind and `NotApplied`, request ID zero, absent observed revision, no affected objects, and no cleanup obligation. Zero is intentional for this context-free codec; the dispatch owner must bind the real request ID. The error sum has no TooLarge: byte-limit violations are InvalidRequest, not queue Busy. Temporary allocations are checked against independent expected lengths before accounting, Alt prefixing or copying. Deterministic mismatch admission is authored; actual allocator failure/null-pointer injection and execution remain untested.

The codec returns a byte array or an error, never partial bytes. This proves only the shape and semantics of the pure API when executed; no queue or terminal state is supplied or observed. Root's later integration must prove no enqueue/PTY prefix after rejection and correct partial-write accounting.

Unsupported Shift-printable, Ctrl-Unicode, Ctrl-Tab/Enter, and other unrepresentable legacy combinations remain mandatory-support gaps. No negotiated ordinary-key protocol, physical-layout transform, native backend capability, or complete tmux wire equivalence is claimed. See `doc/01_research/local/smux_key_encoding_policy_2026_10_26.md`.

V1 history is retained in `doc/09_report/smux_typed_keys_astra_review_2026_10_26.md`: the original 17-case candidate had a P2 unchecked temporary allocation path. V2 adds the production admission seam and two scenarios; source correction does not convert the historical review into a runtime pass.
