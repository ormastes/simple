# smux SendKeys encoding policy research — 2026-10-26

Scope: source research at shared HEAD `4b8a71f7d86549c9823e6e9b2b7dd8b2f25d522c`; other agents' dirty files preserved. No production/test edits, compiler invocations, builds, or backend execution. Native qualification: **NOT_RUN**. This document proposes implementation policy; it does not amend the selected requirements or admit a provider.

## Frozen constraints and decision authority

`caret_mux_tui.md` requirements selected A/N2 on 2026-10-25. REQ-CMUX-003 keeps typed keys distinct from literal input/paste; 006 blocks replacement qualification when required features are absent; 008 requires typed failures and commit evidence; 010/012 require production-connected execution. The detail design requires unsupported checks before polling/mutation. `execution_v1.spl:181` makes every command mandatory: an Unsupported result is not admission success.

`MuxNamedKeyV1` has exactly the 13 entries below; Named and Function have no modifier fields. Scalar carries a Unicode scalar and three booleans, with no physical key, keyboard layout, or keysym field. `request_validation_v1.spl:166` admits 1–256 keys, F1–F24, and all Unicode scalars excluding surrogates; it does not impose a modifier restriction or define keyboard-layout translation.

Root may choose an explicit xterm-compatible byte profile, implement representable inputs, and reject unrepresentable combinations before dispatch within accepted A. It must document constraints and retain admission blockers; it cannot rename the partial subset “full CoreMux.” No new requirement selection is needed to implement correct error handling or negotiated keyboard support. A user decision is required to relax mandatory support, reinterpret modifier booleans as disposable hints, or add a new physical-key/layout contract. Treat the codepoint as the supplied final Unicode scalar, not a US-keyboard position: never uppercase it or turn `2` into `@` merely because Shift is true.

## Exact baseline byte profile

Recommendation: xterm PC-style profile. `smux_backend.spl:29` contains an `xterm-256color` default, but this research has **not** proven the launch path actually installs that TERM or the host terminfo's Backspace choice. Verify those in integration. `ESC` below is byte 27; CSI is `ESC [`; SS3 is `ESC O`; digits are ASCII. Use the target pane's current `application_cursor`, never global/UI state.

| Named | Normal | Application cursor |
|---|---|---|
| Enter | CR (13) | same |
| Escape | ESC (27) | same |
| Tab | HT (9) | same |
| Backspace | DEL (127), declared baseline | same |
| Delete | CSI 3 ~ | same |
| Up / Down / Right / Left | CSI A / B / C / D | SS3 A / B / C / D |
| Home / End | CSI H / F | SS3 H / F |
| PageUp / PageDown | CSI 5 ~ / 6 ~ | same |

Home/End follow [xterm's DECCKM table](https://invisible-island.net/xterm/ctlseqs/ctlseqs.pdf), including application mode. tmux's own pane encoder instead defaults to CSI 1~/4~ for Home/End: do not mix profiles and call them identical. Backspace is configurable across terminal descriptions; DEL is an explicit baseline choice, not a claim that all xterm installations use DEL or that DECBKM is implemented.

| Function | Bytes | Function | Bytes |
|---|---|---|---|
| 1 | SS3 P | 13 | CSI 1;2P |
| 2 | SS3 Q | 14 | CSI 1;2Q |
| 3 | SS3 R | 15 | CSI 1;2R |
| 4 | SS3 S | 16 | CSI 1;2S |
| 5 | CSI 15~ | 17 | CSI 15;2~ |
| 6 | CSI 17~ | 18 | CSI 17;2~ |
| 7 | CSI 18~ | 19 | CSI 18;2~ |
| 8 | CSI 19~ | 20 | CSI 19;2~ |
| 9 | CSI 20~ | 21 | CSI 20;2~ |
| 10 | CSI 21~ | 22 | CSI 21;2~ |
| 11 | CSI 23~ | 23 | CSI 23;2~ |
| 12 | CSI 24~ | 24 | CSI 24;2~ |

These are the [ncurses `xterm+24fkeys` definitions](https://invisible-island.net/ncurses/terminfo.src.html): F13–24 use shifted F1–12 terminal capability strings. This does not claim a physical Shift press, nor require modifyOtherKeys negotiation. Other terminal families number F13–24 differently; no arithmetic “F13 means CSI 25~ through F24” rule is valid across profiles. [Xterm's comparison table](https://invisible-island.net/xterm/xterm-function-keys.html) demonstrates the differences.

## Scalar decision table: explicit legacy support, no silent flag loss

Recommended conservative policy below preserves the meaning of supplied flags. Conventional Ctrl encodings and ESC-prefix Alt are explicit legacy mappings; legacy byte streams are inherently ambiguous and cannot preserve physical event identity. “Supported” means the documented terminal encoding, not that a child can reconstruct every original key event.

Evaluate Shift/Control first; prepend one ESC **only after** successful base encoding when Alt is true. Unsupported means `MuxErrorKindV1.Unsupported`, request ID retained, `NotApplied`, no affected objects and no queued prefix.

| Scalar conditions | Base bytes before optional Alt prefix |
|---|---|
| Control=false, Shift=false | Exact UTF-8 of scalar, including NUL/C0/DEL; never C-string truncation |
| Control=false, Shift=true, codepoint=9 | CSI Z (legacy BackTab) |
| Control=true, Shift=false, ASCII A–Z or a–z | 1–26 respectively |
| Control=true, Shift=false, ASCII `@` through `_`, or backtick through `~` | codepoint AND 31 |
| Control=true, Shift=false, space or `2` | NUL (0) |
| Control=true, Shift=false, `3`, `4`, `5`, `6`, `7` | ESC (27), FS (28), GS (29), RS (30), US (31), respectively |
| Control=true, Shift=false, `/` or `-` | US (31) |
| Control=true, Shift=false, `8` or `?` | DEL (127) |
| Any other Control/Shift combination | Unsupported before dispatch |

Ranges above intentionally overlap consistently. Examples: Ctrl-A = 01; Alt-Ctrl-A = 1B 01; Alt-U+1F600 = 1B F0 9F 98 80; Shift-Tab = 1B 5B 5A. Ctrl-non-ASCII, Ctrl-Tab, Ctrl-Enter, Shift-Enter, Shift-printable, and Ctrl-Shift-printable cannot carry all requested modifiers independently in this baseline and must not silently fall back. In particular, `Scalar('A',false,false,true)` must not become success by forgetting Shift; the caller may send unmodified final `A` only when that is the intended request. Do not reinterpret Shift-`2` as Shift-`@`.

The Ctrl aliases and ESC-prefix convention have primary evidence in [tmux `input_key_vt10x`](https://github.com/tmux/tmux/blob/master/input-keys.c). That implementation also drops Unicode modifiers and contains legacy punctuation remappings; those are compatibility behavior, **not** proof of modifier preservation. This proposal deliberately rejects cases such as Ctrl-1 that tmux may send unchanged. It also rejects Shift-printable instead of assuming Shift was already consumed. These exclusions remain visible constraints and possible admission blockers, not a reduction of mandatory CoreMux scope.

For greater coverage, implement actual per-pane negotiated extended-key modes, reset/query behavior, and application-observed tests before emitting extended ordinary-key sequences. Xterm documents modifier parameter `1 + Shift + 2*Alt + 4*Control`, and modifyOtherKeys formats such as `CSI 27;m;codepoint~`; emission depends on selected mode. See [xterm modified-key discussion](https://invisible-island.net/xterm/modified-keys.html) and [XTMODKEYS controls](https://invisible-island.net/xterm/ctlseqs/ctlseqs.html). Never emit CSI-u/modifyOtherKeys merely because the API has boolean flags or TERM says xterm. Do not claim support for Kitty or Windows keyboard protocols.

## Implementation and evidence ownership

1. **astra_vt_cursor_mode** owns VtModes.application_cursor, reset, `?1h/l`, DECRQM, and the `vt_application_cursor` export. The codec reads this state; it must not duplicate parser mode state.
2. **astra_tmux_audit** currently owns queue/I/O, four facades, `core_mux_input_codec.spl` and `core_mux_input_service.spl`. Root assigns the later key-codec work after that owner completes or explicitly hands it over. No concurrent edits from this research lane.
3. **Later codec owner** adds a pure all-keys encoder returning exact bytes or typed error. Validate/encode all entries and final capacity before queue admission. Unsupported key N must leave keys 0..N-1 unsent. Keep the byte buffer intact through partial PTY writes and owner result handling; never retry an unknown-commit mutation as if NotApplied.
4. **Later test owner** authors real byte-equality assertions for every Named/F1–24 entry; all control-map boundaries; NUL, multibyte and supplementary scalars; all eight modifier combinations on representative ASCII/Unicode; both cursor modes; invalid scalars/F0/F25; late unsupported keys; queue full/closed and partial writes. Raw-mode child tests must observe exact bytes through production CoreMux for both backends and verify no queued prefix on rejection. Confirm TERM/terminfo compatibility and per-pane mode isolation. No executable placeholders are created here.
5. **Root/final reviewer** reviews the terminal profile and constraints against callers, then verifies accepted A without weakening requirements. All tests, Phase2/Phase3 compilation, backend execution, and full CoreMux/native qualification remain **NOT_RUN** in this research lane.

Evidence access: context fetch/index succeeded for primary sources; context shell returned exit -1 and JavaScript reported missing Node. Bounded PowerShell reads and primary-domain web search supplied the missing snippets. Upstream master URLs are mutable observations dated above, not pinned release proofs.
