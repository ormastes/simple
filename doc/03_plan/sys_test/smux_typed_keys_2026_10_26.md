# Smux typed-key execution plan — 2026-10-26

Status: **PLANNED / NOT_RUN**. REQ-CMUX-003/006/008/010/012. Source scope is a pure codec, not provider dispatch. No executable system spec or placeholder is created for missing effects.

## Existing source controls

`core_mux_key_codec_spec.spl` v2 contains 19 authored unit scenarios against `src/os/apps/smux/core_mux_key_codec.spl`, including deterministic production temporary-allocation mismatch admission. These cases do not inject or prove an actual OOM/null allocation. Run once with root's admitted producer/runtime/provider and actual SSpec execution after source review. Record real counts, exit status and source/compiler hashes. Docgen and SSpec maintenance remain pending. A parse/discovery-only result is not execution.

## Raw-mode fixture gate

The existing `test/fixtures/coremux/literal_input_child.spl` opens the selected terminal-console owner, reads text, and compares a Unicode string ending in CR. This research/implementation lane has no execution proof of its actual host mode or exact raw byte reporting. Its `channel` path does not observe child input. Do not reuse it as an exact key-byte oracle yet; do not add a fake “ready” or skip-as-pass test.

Before reuse, inspect the selected terminal owner and prove that the actual child uses an input mode disabling line buffering, echo, signal/control handling and newline conversion as needed for byte observations. On Windows, establish whether the selected console input API reports decoded key events/text rather than the encoded VT byte stream; a text/event observation is not raw PTY-byte equivalence. Use existing selected owners only, no foreign ABI. If the existing fixture cannot produce exact observations, keep these scenarios PLANNED and assign a separately reviewed fixture/owner improvement.

## Required production-connected scenarios

| Scenario | Observation needed before qualification |
|---|---|
| Named/F1–24 | Real CoreMux SendKeys dispatch to an owned raw-input child yields each expected profile-specific sequence; child identity and TERM/terminfo are recorded. |
| Per-pane DECCKM | Child output enables `?1h`, resets with `?1l`, and queries mode; target pane Up/Home/End follow ingested state while a second pane stays unchanged. |
| Unicode and legacy modifiers | Exact NUL, UTF8 boundary samples, Alt prefix, Ctrl aliases and Shift-Tab bytes reach the child in order. |
| Unsupported suffix | A request containing valid prefix plus unsupported key returns Unsupported/NotApplied and leaves the real queue and child input unchanged. Use bounded nonblocking observation and a subsequent known marker, not silence alone. |
| Capacity and partial writes | Whole-request queue admission is atomic; exact residual bytes survive actual short/pending PTY writes without replay. Codec budget errors remain separate from owner queue Busy. |
| Receipt correlation | Context-free request ID zero is replaced with the actual request ID by the service; Unknown/Partial/Applied evidence follows actual effects. |
| Separate backend semantics | Smux uses its declared xterm profile; tmux uses its native TERM-aware adapter. Assert semantic events with each backend's terminfo, not universal byte equality. |
| Modifier admission gaps | Unsupported cases remain visible in constraints and block any mandatory workflow relying on them. Full-provider admission stays unqualified until required semantics have actual evidence. |

Fixture launch, bounded deadlines, output capture and cleanup must use existing owned Sosix/terminal owners and root-approved scope. Preserve source, producer generation, runtime/provider, binary hashes, commands, stdout/stderr, child exit/handle state, and actual observation artifacts. No builds or runtime execution occurred in this lane; no success counts exist.
