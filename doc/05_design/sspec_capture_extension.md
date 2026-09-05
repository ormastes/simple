# Design: Extendable SSpec Capture System

Status: design · 2026-07-05 · Domain: app / spipe
Requirements: `doc/02_requirements/feature/sspec_scenario_manual.md` (FR-1..FR-6)
Target output: `doc/07_guide/app/spipe/scenario_manual_example.md`
Pipeline touched: `src/app/spipe_docgen/spipe_docgen/{generator,common}.spl`

## Goal

One capture abstraction that (a) covers the six built-in kinds a scenario manual
needs and (b) lets a user spec register its own kind without patching the
compiler or `spipe_docgen`. A capture produces a golden-comparable artifact and
renders itself into the generated md. `spipe_docgen` must never break on a kind
it does not know.

Built-in kinds: `tui_grid`, `gui_image`, `protocol_json`, `protocol_binary`,
`bit_table` (8/16/32-bit aligned views), `statistics` (mean/stddev/percentile vs
golden with tolerance).

## 1. The `Capture` trait

Composition only — no inheritance. A concrete capture is a plain struct that
holds its captured bytes plus a `ComparePolicy`, and implements `Capture`.

```simple
enum Audience:
    User        # end-user manual: clean voice, no golden badges
    Qa          # developer/QA doc: everything visible

struct CaptureResult:
    passed: bool
    summary: text          # one-line verdict, e.g. "3 cells differ in status_line"
    diff_md: text          # rendered diff block, "" when passed or not applicable

trait Capture:
    fn kind() -> text                                   # stable id, e.g. "tui_grid"
    fn name() -> text                                   # capture instance name
    fn capture() -> Result<bool, text>                  # record live artifact into self
    fn compare(golden: [u8], policy: ComparePolicy) -> CaptureResult
    fn render_md(audience: Audience) -> text            # the md fragment to embed
    fn serialize() -> [u8]                              # bytes written to the golden file
    fn ext() -> text                                    # golden file extension, e.g. "txt"
```

`deserialize` is not on the trait: goldens are opaque `[u8]` handed to
`compare`, so a kind never needs to reconstruct a peer object. That keeps the
surface minimal — capture, compare, render, serialize is all six built-ins need.

Built-in structs (each `impl Capture for ...`):

| kind | struct | serialize | render_md |
|------|--------|-----------|-----------|
| `tui_grid` | `TuiGridCapture` | char grid `.txt` | fenced `text` grid + region diff |
| `gui_image` | `GuiImageCapture` | `.ppm`/`.png` | `![]()` image embed |
| `protocol_json` | `JsonCapture` | pretty `.json` | fenced `json` block |
| `protocol_binary` | `BinaryCapture` | raw `.bin` | offset\|hex\|field\|value table |
| `bit_table` | `BitTableCapture` | raw `.bin` | 8/16/32-bit aligned tables |
| `statistics` | `StatsCapture` | `.sdn` numbers | mean/stddev/percentile table |

## 2. Registry — register at spec-runtime, render generically at docgen

Two independent surfaces. They never share process, so they never share state —
the golden file on disk is the only contract between them.

**Spec-runtime registry** (in the test process). A support module registers a
factory keyed by kind id; scenario helpers look it up.

```simple
struct CaptureRegistry:
    factories: Map<text, fn() -> Capture>

    fn register(kind: text, make: fn() -> Capture)
    fn make(kind: text) -> Result<Capture, text>
```

Built-ins are registered at framework init. A user spec registers extra kinds in
its own support module before any scenario runs:

```simple
capture_registry().register("audio_wave", fn() -> Capture: AudioWaveCapture.empty())
```

When a capture runs it emits a sidecar `<name>.capture.sdn` next to the golden
recording `kind`, `name`, `audience_tags`, `result.passed`, and `result.summary`.
`spipe_docgen` reads those sidecars — it never imports the user's Simple code.

**Docgen rendering.** `spipe_docgen` groups artifacts by declared display policy
(`embed_all` / `links` / `embed_tui`, from `evidence_display_policy` in
`common.spl`). For a known extension it uses the matching embed group. For an
**unknown kind** it falls back to a generic block so docgen never breaks:

```
#### {name}  ({kind})
```text
<serialized golden, or "binary artifact — see {path}" when non-text>
```
Result: PASS   (golden: {path})
```

Fallback rule: text-ish serialization (`.txt/.json/.sdn/.log`) is fenced inline;
anything else becomes a link plus the pass/fail line. This is the safety net —
a user kind with no docgen plugin still produces a correct, if plain, section.

## 3. Compare policies (declared at the call site)

```simple
enum ComparePolicy:
    Exact
    Masked(fields: [text], regions: [Rect])     # ignore these before comparing
    Tolerance(abs: f64, rel: f64)               # numeric bands (statistics/bit)
    Scoped(component_ids: [text])               # compare only these ids/regions
```

The policy is passed where the capture is taken, so intent lives with the
scenario, not in a global config:

```simple
capture_tui("add_task", ComparePolicy.Scoped(["task_list", "input_bar", "status_line"]))
capture_stats("latency", ComparePolicy.Tolerance(abs: 0.0, rel: 0.02))
capture_json("sync_req", ComparePolicy.Masked(["timestamp", "request_id"], []))
```

`compare` interprets the policy per kind: `tui_grid` honors `Scoped`/`Masked`
regions and drops the rest (clock, spinner); `statistics`/`bit_table` honor
`Tolerance`; `protocol_json` honors `Masked` field names and is field-order
insensitive.

## 4. Golden storage & update flow

Layout mirrors the spec path, one dir per spec:

```
test/03_system/app/todo/todo_tui_spec.spl
test/03_system/app/todo/goldens/todo_tui_spec/
    add_task.txt          # tui_grid recording
    add_task.capture.sdn  # sidecar: kind, name, audience, result
    sync_req.json
    latency.sdn
```

Path = `<spec_dir>/goldens/<spec_stem>/<capture_name>.<ext>` where `ext = capture.ext()`.

Update flow:
- No golden present → **first-run auto-write** the recording and mark the capture
  `pending-review` in the sidecar (does not count as pass).
- `bin/simple test --update-golden [path]` → overwrite goldens for the selected
  specs, each rewrite tagged `pending-review`.
- **Review gate:** a `pending-review` golden fails `bin/simple build check` until
  a human clears it (`bin/simple test --accept-golden <path>` flips the tag to
  `reviewed` and stamps the run id). Goldens are committed; the flip is a diff a
  reviewer sees. No silent golden churn.

## 5. md rendering contract per audience

`render_md(audience)` feeds the existing generator embed groups in
`generator.spl`; the capture kind decides content, the generator decides layout.

| audience | groups used | what is stripped |
|----------|-------------|------------------|
| `Qa` (default) | `append_embedded_media_group`, `append_tui_text_capture_group`, `append_evidence_table_group` | nothing — golden badges, diffs, protocol tables all shown |
| `User` | image + tui-text groups only | golden badges, source attributions, diff blocks, protocol_* kinds (routed to the qa doc); run results collapse into Appendix A |

Concretely: `tui_grid.render_md(User)` returns just the fenced `text` grid (the
`<details>` wrapper and diff are `Qa`-only); `render_md(Qa)` appends the
region-scoped char diff when `!passed`. `protocol_json`/`protocol_binary` return
`""` for `User` so audience filtering needs no special-casing in the generator —
an empty fragment simply contributes nothing. This reuses
`should_embed_evidence_media` / the `embed_all|links|embed_tui` policy unchanged;
audience only gates which fragments are non-empty.

## 6. Adding your own capture kind — worked example

Goal: capture an audio waveform, compare RMS against a golden within tolerance,
show a sparkline in the manual. About 20 lines plus registration.

```simple
use spipe.capture   # Capture, CaptureResult, ComparePolicy, Audience, capture_registry

struct AudioWaveCapture:
    name_: text
    samples: [f64]
    policy: ComparePolicy

    static fn empty() -> AudioWaveCapture:
        AudioWaveCapture(name_: "", samples: [], policy: ComparePolicy.Exact)

impl Capture for AudioWaveCapture:
    fn kind() -> text: "audio_wave"
    fn name() -> text: self.name_
    fn ext() -> text: "sdn"
    fn capture() -> Result<bool, text>:
        self.samples = audio_probe_last_buffer()   # user's app hook
        Ok(true)
    fn serialize() -> [u8]: sdn_encode_floats(self.samples)
    fn compare(golden: [u8], policy: ComparePolicy) -> CaptureResult:
        val want = rms(sdn_decode_floats(golden))
        val got = rms(self.samples)
        val ok = within_tolerance(got, want, policy)   # reads Tolerance bands
        CaptureResult(passed: ok, summary: "rms {got} vs {want}", diff_md: "")
    fn render_md(audience: Audience) -> text:
        "```text\n{sparkline(self.samples)}\n```\n"
```

Register once in the test support module, then use it in a scenario:

```simple
capture_registry().register("audio_wave", fn() -> Capture: AudioWaveCapture.empty())

# in a scenario:
capture("audio_wave", "chime", ComparePolicy.Tolerance(abs: 0.01, rel: 0.0))
```

Generated md (user audience) — the sparkline fragment embedded like any TUI text
capture, with a golden line only in the qa doc:

```text
▁▃▅█▇▄▂▁
```

If the user forgets a docgen plugin, the §2 fallback still emits the fenced
sparkline plus `Result: PASS (golden: .../chime.sdn)` — docgen degrades, never
breaks.

## Non-goals

- No cross-kind diff algebra — each kind owns its own `compare`.
- No live golden editing UI — review is a git diff on committed goldens.
- No new display-policy vocabulary — reuse `embed_all|links|embed_tui`.
```
