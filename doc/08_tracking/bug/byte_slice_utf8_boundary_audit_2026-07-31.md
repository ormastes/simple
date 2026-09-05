# Audit: byte-indexed `.slice()`/`.substring()` splitting UTF-8 codepoints

**Date:** 2026-07-31
**Scope:** Follow-up to `8151c391932` ("fix(interpreter): byte-transparent text
slices"), which made the interpreter's `.substring()`/`.slice()` byte-indexed
to match `.find()`/`.index_of()` (already byte-based) and the native runtime
`rt_slice` (already byte-based, raw pointer arithmetic). This audit asks: what
happens when a slice boundary that is **not** derived from `.find()`/
`.index_of()` lands in the middle of a multi-byte UTF-8 codepoint?

This is an audit only. No fixes were applied.

## 1. Measured behavior at a split boundary

### 1a. Interpreter (`bin/simple test` lane — tree-walk interpreter)

**MEASURED.** Ran the existing spec
`test/01_unit/bugs/text_slice_substring_spec.spl` (`SIMPLE_TIMEOUT_SECONDS=900
timeout 900 bin/simple test test/01_unit/bugs/text_slice_substring_spec.spl
--timeout 900`): **76 total, 76 passed, 0 failed.** This spec's "codepoint-
boundary safety" group explicitly pins the behavior: slicing `"café"` at
byte range `[3,4)` (the lead byte of `é` without its continuation byte)
returns `"\u{FFFD}"` (`char_code_at(0) == 65533`), and the same for a 3-byte
CJK char and a 4-byte emoji. Source:
`src/compiler_rust/compiler/src/interpreter_method/string.rs:301-328` — the
`"slice" | "substring"` arm does `String::from_utf8_lossy(&bytes[start..end])`,
which substitutes U+FFFD for any byte sequence that doesn't decode as valid
UTF-8.

**Conclusion: the interpreter is benign.** It never panics and never emits
invalid UTF-8 — a split boundary always yields a well-formed (if lossy)
string.

### 1b. Native/JIT lane (`bin/simple run`, and native-build — both lower `.slice()`/`.substring()` to `rt_slice`)

**MEASURED** (probe files written to
`/tmp/claude-1000/.../scratchpad/utf8_slice_probe{3,4}.spl`, run via
`bin/simple run` — confirmed via `grep -rn rt_slice
src/compiler_rust/compiler/src/{codegen,method_registry,pipeline}` that both
the Cranelift JIT and LLVM native-build backends lower `.slice()`/
`.substring()` to the same C runtime call `rt_slice`):

```
val s = "café"
val bad = s.slice(3, 4)
print("LEN=" + bad.len().to_string())   # => LEN=1
print(bad)                               # stdout bytes: ef bf bd 0a
```

`.len()` reports **1** (a single raw byte), not 3 (what a U+FFFD
substitution, `ef bf bd`, would report) and not 0. This is only possible if
the runtime string object was constructed by copying the raw split byte
(`0xC3`, the lead byte of `é`) verbatim, with **no UTF-8 validation** — which
matches reading `rt_slice` in `src/runtime/runtime_native.c:3067-3128`: for
the `stride == 1` case it calls
`rt_string_new((const uint8_t*)s->data + begin, (uint64_t)(finish - begin))`,
a raw pointer-arithmetic byte copy with no codepoint-boundary check anywhere
in the function.

The `print(bad)` output was, confusingly, the 3-byte UTF-8 encoding of
U+FFFD (`ef bf bd`), **not** the raw 1-byte content `.len()` reports. This
means the print/stdout path applies its own defensive lossy-UTF-8
sanitization at *display* time, independent of the string object's actual
stored bytes — i.e., printing to a terminal masks the corruption, but the
string value itself (as measured by `.len()`) holds the invalid 1-byte
sequence and would propagate it to any other consumer (further
slicing/concatenation, hashing, file/network write, GUI `draw_text`,
equality comparison) that doesn't apply the same terminal-output sanitizer.

**Conclusion: the native/JIT lane is NOT benign.** A split boundary produces
a text value whose backing bytes are genuinely invalid UTF-8 (a truncated
multi-byte sequence), silently, with no panic and no error — confirmed by a
byte-length that only a raw truncating copy explains.

*(Side anomaly, not chased further — out of scope: `bad.char_code_at(0)`
returned `192` in one probe run instead of the expected raw byte value `195`
(0xC3). `rt_string_char_code_at` is CHARACTER-indexed, not byte-indexed
(`src/runtime/runtime_native.c:2303-2357`, confirmed by comment at
`:2363-2368` contrasting it with the byte-indexed `byte_at`), and 1-byte
strings go through a global short-string intern cache keyed by
`byte_value + 1` (`rt_string_new`, `:2046-2066`). Something in that
interaction returns a wrong value; this looks like an independent latent
bug in `char_code_at`/the short-string cache, not part of this audit's
scope. Flagging for a separate investigation, not filing a fix here.)*

## 2. Because the native/JIT lane produces invalid UTF-8 → survey call sites

Per the task instructions, since behavior is NOT benign, call sites in owned
code were surveyed. **This survey is NOT an exhaustive per-site manual
classification** — the raw count is far too large for that within this
audit's scope; see the honesty note at the end of this section.

### Raw counts (MEASURED via grep)

```
grep -rn --include=*.spl -E '\.substring\(|\.slice\(' src/ \
  | grep -v '^src/compiler_rust/vendor/' \
  | grep -v '^src/runtime/vendor/' \
  | grep -v '^src/compiler_rust/lib/std/'
```

**Total: 7,218 call sites** across owned `.spl` code (vendored paths and the
dormant `src/compiler_rust/lib/std/` excluded per instructions; `src/i18n/`
has zero sites).

Top directories by count: `src/lib/gc_async_mut` (1,173), `src/lib/
nogc_sync_mut` (938), `src/app/llm_caret` (637), `src/lib/nogc_async_mut`
(523), `src/app/cli` (360), `src/lib/common` (355), `src/compiler/
35.semantics` (307), `src/app/compile` (305), `src/lib/editor` (294),
`src/app/office` (269).

### Classification methodology and its limits (INFERRED / heuristic, not exhaustive)

A same-line grep for `index_of`/`find`/`rfind`/`last_index_of` in the
argument expression found only **27** sites — this drastically *undercounts*
true SAFE sites, because the common and, from sampling, dominant pattern in
this codebase is: a boundary variable (`idx`, `dot`, `colon_idx`, `cursor`,
`relative`, `end`) is computed by `.index_of()`/`.find()`/a byte-scanning
`while` loop **on a preceding line**, then used in the slice call — invisible
to a single-line grep. Manually reading representative files (below)
confirms this pattern is common and is SAFE.

A second heuristic — `.substring(0, N)` / `.slice(0, N)` with a literal
`N >= 10` (the classic "truncate for display, append `...`" pattern, the
archetype of an AT-RISK site) — found **31 live call sites** (2 additional
hits were inside commented-out example code and excluded). These 31 were
individually read for context; results below.

**Given 7,218 total sites, a full per-site manual audit was not performed.**
What follows is: (a) full manual classification of the 31 literal-truncation
sites (the highest-signal AT-RISK pattern), (b) manual verification of ~15
additional sampled sites in risk-plausible directories (editor JSON/CLI
parsing, LLM chat/session/config parsing) that all turned out SAFE via the
"boundary = find-offset, or find-offset + length of a known ASCII literal,
or `.len() - N` immediately guarded by `.ends_with(<N-byte ASCII literal>)`"
pattern. This pattern recurs enough across the sampled files that it appears
to be the dominant idiom in this codebase — but that is an inference from a
sample, not a measurement over all 7,218 sites.

### Classified counts (of the 31 literal-truncation sites — the AT-RISK-pattern subset, NOT the full 7,218)

- **AT RISK: 11** — truncates plausibly-non-ASCII user/LLM/document/UI text
  at a hardcoded byte count with no boundary check.
- **SAFE: 3** — boundary is a hex-digest/fingerprint (`stable_id.spl`,
  `incremental.spl`) or is otherwise ASCII-only by construction.
- **UNCLEAR / not fully verified: 17** — plausible display-truncation of
  text that could originate from user/LLM content, based on file/variable
  naming, but the exact provenance of the sliced value was not traced back
  to its ultimate source for every one of the 17 in the time available.
  Classify these as AT RISK by default per the task's guidance ("AT RISK ...
  AND the input can plausibly be non-ASCII") since most are chat/tool/log
  preview truncations in `app/llm_caret/claude_full/*` and
  `app/llm_dashboard/*`.

The remaining ~7,187 sites were not individually classified. Directory-level
sampling (CLI flag parsing in `app/llm_caret/main.spl`, JSON field
extraction in `app/llm_caret/claude_api.spl`/`openai_api.spl`, editor
LSP-JSON parsing in `app/editor/editor_ctrl_lsp2.spl`, markdown/link/
attachment helpers in `app/editor/editor_markdown_helpers.spl` and
`editor_attachment_template.spl`) found these all SAFE (find-derived or
known-ASCII-literal-length arithmetic). This is consistent with, but does
not prove, a low AT-RISK rate across the unclassified majority.

## 3. Top risk sites (file:line + reasoning)

1. `src/app/llm_caret/chat.spl:181` — `summary.substring(0, 200)` where
   `summary = redact(result.content)` and `result.content` is arbitrary tool
   output (file contents, command output, LLM text) — genuinely
   unconstrained and plausibly non-ASCII. **AT RISK.**
2. `src/lib/nogc_async_mut/llm_diagnostics/transcript_parser.spl:88` —
   `msg_content.slice(0, 200)` on LLM chat transcript content pulled from a
   JSON `"content"` field — multilingual chat transcripts are exactly the
   non-ASCII case. **AT RISK.**
3. `src/os/compositor/simple_gui_hosted_wm.spl:408` — `label.substring(0,
   12)` truncating a window title before `self.backend.draw_text(...)` —
   window titles can be non-ASCII app names; this is OS/compositor code, so
   a split boundary here (invalid UTF-8, confirmed above, not just a
   replacement char on this lane) reaches a text renderer directly. **AT
   RISK, elevated by consequence (board-runnable GUI code).**
4. `src/app/office/sheets/access_controller.spl:309` — `line.substring(0,
   124)` truncating spreadsheet cell/line content for a fixed-width text
   frame — spreadsheet content is arbitrary user/business data, plausibly
   non-ASCII (international text, formulas). **AT RISK.**
5. `src/lib/nogc_sync_mut/stomp/utilities.spl:33` — `body.substring(0, 50)`
   previewing a STOMP message body — generic messaging payloads are commonly
   text/JSON and can carry unicode. **AT RISK.**
6. `src/app/mcp/main_lazy_assistant.spl:58` — `prompt.slice(0, 160)` on a
   raw user prompt. **AT RISK.**
7. `src/app/mcp/main_lazy_assistant.spl:51` — `preview.slice(0, 48)`, same
   file, same concern. **AT RISK.**
8. `src/app/llm_caret/claude_full/utils/analyzeContext.spl:14` —
   `value.substring(0, 40)` on context/content text feeding an LLM-agent
   utility. **AT RISK.**
9. `src/app/llm_caret/claude_full/services/tools/StreamingToolExecutor.spl:168`
   — `tool.block.inputSummary.slice(0, 40)` — tool input summaries can embed
   arbitrary (non-ASCII) argument text. **AT RISK.**
10. `src/app/llm_dashboard/scheduler/scheduler.spl:32,44` —
    `prompt.slice(0, 40)` used to build a task display name from a raw user
    prompt. **AT RISK.**
11. `src/app/test/extract.spl:376` — `example.context.substring(0, 100)` —
    doc/example text extracted for reporting; plausibly non-ASCII if any
    source doc uses unicode. **AT RISK (lower likelihood, still plausible).**

Contrast — confirmed SAFE despite matching the same literal-N grep pattern:
- `src/compiler/35.semantics/symbol_id/stable_id.spl:64` —
  `digest.slice(0, 32)` on a hash-digest string (hex-only, ASCII by
  construction). **SAFE.**
- `src/compiler/80.driver/driver_build/incremental.spl:100` —
  `digest.substring(0, 16)` — same hex-digest reasoning. **SAFE.**
- `src/app/llm_caret/session.spl:244` — `e.substring(0, e.len() - 5)`,
  immediately guarded by `e.ends_with(".json")` on the preceding line — 5
  is the exact byte length of the known ASCII suffix `.json`, so the
  boundary is always byte-safe regardless of what precedes it. **SAFE.**
- `src/app/llm_caret/config.spl:138` — `trimmed.substring(0, trimmed.len()
  - 1)`, guarded by `trimmed.ends_with(":")` — same pattern, 1-byte ASCII
  suffix. **SAFE.**
- `src/app/editor/editor_ctrl_lsp2.spl:280-290` — `cursor = cursor +
  relative + 11`, where `relative` is a `.find()`-derived byte offset of the
  ASCII JSON token `"startLine"` (11 bytes) — advances by exactly a
  found-substring's own byte length. **SAFE**, and representative of the
  dominant idiom seen across `app/editor/*` and `app/llm_caret/*` JSON/CLI
  parsing.

## 4. Bottom line

- Interpreter (`simple test` lane): **benign** — lossy U+FFFD substitution,
  never invalid UTF-8, never a panic. Confirmed by an existing spec's full
  76/76 pass.
- Native/JIT lane (`simple run`, native-build — the production path per
  `.claude/rules/bootstrap.md`, and the one the interpreter's own safety net
  does NOT cover): **not benign** — `rt_slice` performs a raw, unvalidated
  byte copy and can produce a text value holding a genuinely invalid,
  truncated UTF-8 byte sequence. This is silent (no error, no panic) and can
  be partially masked at `print()`/terminal time by an apparently separate
  defensive sanitizer, while still being present in the string value itself
  for any other consumer.
- Because the native/JIT lane is not benign, call sites were surveyed
  (§2-3). Of the 31 sites matching the highest-signal "hardcoded literal
  truncation" pattern, 11 are clear AT RISK, 3 are clear SAFE (hex
  digests), and 17 are plausible-but-unverified AT RISK by default. The
  remaining ~7,187 of the 7,218 total call sites were not individually
  classified; directory-level sampling suggests SAFE (find-derived or
  known-ASCII-literal-length-arithmetic) boundaries dominate, but that is an
  inference from a sample, not a measurement over the full set.

No fixes were applied — this is an audit only, per instructions.
