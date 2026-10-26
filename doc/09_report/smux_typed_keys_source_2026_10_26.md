# Smux typed-key codec source handoff — 2026-10-26

**SOURCE AUTHORED; native/runtime qualification NOT_RUN.** Starting shared HEAD: `4b8a71f7d86549c9823e6e9b2b7dd8b2f25d522c`. Other agents' dirty work preserved. Root approved this five-new-file manifest; no production owner, common contract, queue, facade, VT, foreign ABI, or existing test was changed.

| New path | Purpose |
|---|---|
| `src/os/apps/smux/core_mux_key_codec.spl` | Pure `core_mux_keys_bytes_v1(keys: [MuxKeyV1], application_cursor: bool, max_bytes: i64) -> Result<[u8], MuxErrorV1>`. |
| `test/01_unit/os/apps/smux/core_mux_key_codec_spec.spl` | 17 real production-code unit scenarios, zero executed. |
| `doc/06_spec/01_unit/os/apps/smux/core_mux_key_codec_spec.md` | Authored manual mirror with explicit limitations. |
| `doc/03_plan/sys_test/smux_typed_keys_2026_10_26.md` | Native production-connected scenario plan; no executable placeholders. |
| `doc/09_report/smux_typed_keys_source_2026_10_26.md` | This source handoff and evidence status. |

## Behavior and bounds

All 13 Named keys and F1–24 have concrete xterm-profile encodings. Six cursor keys, including Home/End, depend solely on the passed application-cursor boolean. Scalar input encodes exact UTF8, admitted ASCII Ctrl aliases, ESC-prefix Alt and Shift-Tab. The codepoint is a supplied Unicode scalar, not a physical keyboard-layout position. No flag is silently dropped and no extended ordinary-key protocol is emitted.

The codec validates 1–256 keys and 0–65536 capacity, then preflights the whole output before allocating the final exact-size buffer. Bounded two-pass encoding avoids mutable nested-array storage; maximum output is 1792 bytes, seven per key. Request/count/scalar/function/budget violations use existing InvalidRequest; unsupported modifiers use Unsupported; checked output/prefix allocation failure uses Unavailable. All errors carry NotApplied, request ID zero, no observed revision/affected objects/cleanup obligation. No queue is read, so no Busy result is fabricated. The later owner must correlate request IDs and distinguish capacity from live backpressure.

## Open gaps and review boundaries

- Shift-printable, Ctrl-Unicode, Ctrl-Tab/Enter and other unsupported legacy modifier combinations remain unimplemented semantics and qualification blockers where required. This is not full CoreMux admission.
- No SendKeys dispatch/queue integration is added. The raw I/O author owns `core_mux_input_codec.spl` and `core_mux_input_service.spl`; this lane does not edit them. VT mode work is independent and consumed later through the boolean parameter.
- The selected Smux xterm profile uses normal/application Home/End. Tmux's later native TERM-aware adapter may produce different bytes; global wire equivalence is not claimed. Actual TERM installation and Backspace/terminfo consistency need integration evidence.
- Existing text-console fixture is not yet proven an exact raw-byte child oracle. Native scenarios remain a plan, not stub tests or fake passes.
- Real allocation-failure injection has no test; neither branch coverage nor parser/compiler correctness is measured. Source assertions do not constitute native effects or full-port support.

Compiler/build/SSpec/runtime/docgen/maintenance executions: **0**. Native processes launched: **0**. Commits/staging: **0**. Source-only inspection is not verification PASS. Root must obtain independent review of these exact paths before any later admitted execution or landing.

## V2 correction — independent P2 temporary-allocation finding

V1 above is retained as history, not current admission. The independent review in `smux_typed_keys_astra_review_2026_10_26.md` found that literal/UTF8 temporary arrays could fail allocation and report length zero. First-pass counting could undercount; the second pass could silently omit a key and return a zero-filled tail; Alt could prefix a missing base. Runtime source evidence, not executed fault injection, established this risk. V1 source SHA256 was `0ec80a4e6adf2df2d7fc2898c096e89da326b7ca13f3af7f468366e602d70488`; V1 spec SHA256 was `f420c76b4a138d8e25098756f2c1fca1b972ccb7403c8aab6179f85acd63a72a`. The review preserves all five V1 pins.

V2 base HEAD is `fd744829aea0e0d7f568cd2286702a1a9cf37c2d`. The same five-path manifest applies. `core_mux_key_bytes_checked_v1(expected_length: i64, bytes: [u8]) -> Result<[u8], MuxErrorV1>` is an owner-local production admission seam, not a shared wire contract. Every Named, Function, Control and UTF8 literal now passes an independent constant expected length before any size accounting, Alt prefixing or copying; Alt's checked base determines its checked prefix size. The final output retains its allocation check and additionally requires copied length to match preflight length. Missing, shortened or oversized carriers return typed Unavailable/NotApplied. No successful supported key has an empty representation.

V2 has **19 authored scenarios / 19 steps, zero executed**, including two deterministic mismatch/exact-length controls on the actual production seam. These do not claim real OOM, null-pointer injection or native effects. The original P2 review remains unchanged; focused independent re-review is pending. All modifier/dispatch/TERM/fixture gaps and NOT_RUN statuses remain. No compiler/build/test/docgen/maintenance invocation, staging or commit occurred during this correction.
