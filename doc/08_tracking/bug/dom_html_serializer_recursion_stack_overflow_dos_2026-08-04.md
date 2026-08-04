# DOM→HTML serializer recursed per depth: a hostile page aborted the renderer (2026-08-04)

**Status:** FIXED
**Severity:** High — remotely triggerable denial of service of the browser-engine renderer
**Component:** `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl`
**Spec:** `test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl`

## Symptom

`_be_dom_collect_html` — the DOM→HTML serializer behind `be_dom_serialize_html`,
`be_dom_serialize_html_for_render` and `be_dom_serialize_children` — recursed
once per DOM level. Serializing a chain 513 nodes deep exhausted the native
stack and killed the process outright:

```
thread 'simple-main' (2372418) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

## Why it was reachable

`html_tree_builder.spl` admits documents up to `HTML_MAX_TREE_DEPTH` = 512, and
`dom_accessors.spl` declares a matching `BE_DOM_HTML_SERIALIZE_MAX_DEPTH` = 512
guard. A hostile page reaches 513 levels with 513 `<div>` tags, so the intended
guard was effectively unreachable: the process died before the check could fail
closed. Any path that serializes untrusted markup (render, innerHTML readback,
devtools inspection) aborted the whole renderer instead of returning an error.

## Why the existing spec did not catch it

The hardening spec already asserted "accepts depth 512 and fails closed at depth
513", but its `_deep_serialization_dom` helper was **vacuous**. It walked a
top-down `cursor`, and `add_child` stores a COPY, so every append mutated a
detached copy and never reached `root`. The helper returned a single flat
`<div></div>` at every requested depth, so the depth assertions measured one
node instead of a chain — the guard they claimed to exercise was never reached.

The helper now builds bottom-up (`parent.children.push(chain)`), which produces
a genuine 513-deep chain and immediately reproduced the abort. This is the
load-bearing part of the finding: the test was green for the entire time the
DoS was live.

The abort also **truncated the suite**, which is why the before/after example
counts below differ by more than one failure: the crash killed the run
mid-suite, so 2 further examples never executed and were never counted.

## Fix

`_be_dom_collect_html` is now iterative, driven by an explicit work stack. The
per-node markup was split into two helpers so the walk itself carries no
recursion:

- `_be_dom_open_html_node(node, render_only, state) -> bool` (`dom_accessors.spl:179`)
  — emits `<tag …>` or escaped text, returns whether children still need walking.
- `_be_dom_close_html_node(node, state)` (`:223`) — emits `</tag>` (nothing for
  `#document`).
- `_be_dom_collect_html` (`:234`) — three parallel frame stacks (`frame_nodes`,
  `frame_next`, `frame_count`) plus a `top` cursor.

Depth is now bounded by the heap, and `BE_DOM_HTML_SERIALIZE_MAX_DEPTH` fires
and fails closed (empty output, `state.failed`) instead of aborting.

### Avoiding the O(n²) clone trap

Arrays are value types here and `.push` clones, so a naive stack push per node
would turn an O(n) walk into O(n²) on a hot path. The frame stacks are therefore
**grown only while descending past the deepest level reached so far** — at most
`BE_DOM_HTML_SERIALIZE_MAX_DEPTH` pushes for an entire document, irrespective of
node count — and are afterwards **reused in place by index assignment**
(`frame_nodes[top] = child`). A 5,000-sibling list performs zero additional
pushes. Child counts are cached in `frame_count` so `.len()` is not re-read per
sibling. Per-node work is O(1) amortized.

## Measurements

External timer only (wall-clock around a single-purpose script); in-language
benchmarks are not trusted in this repo. Serialization cost is isolated by
timing a build-only script and a build-plus-20-serializations script and
dividing the median difference by 20. 5 reps per configuration, medians shown.

| DOM shape | before | after | ratio |
|---|---|---|---|
| wide: 5,000 `<span>` siblings, depth 5 (3,101,120 bytes out) | 149.3 ms | 127.0 ms | **0.85x** (faster) |
| deep: parsed 400-level `<div>` nest (88,780 bytes out) | 18.5 ms | 1.5 ms | **~12x faster** |

Raw medians (ms): wide build 499→322, wide full 3485→2862; deep build 756→660,
deep full 1126→690.

Output bytes are byte-identical before and after on both shapes (3,101,120 wide
/ 88,780 deep), so the speedup is not a truncation artifact. The wide case — the
one at risk from the clone trap — got *faster*, well inside the ~1.2x regression
budget.

Fail-closed behaviour after the fix (previously an abort):

```
depth511_len=5621
depth513_len=0 fails_closed=true
depth4001_len=0 fails_closed=true
SURVIVED
```

Depth 4001 is far past the cap and still returns cleanly, so the guard fails
closed rather than relying on native stack headroom.

## Verification

- `test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl`
  - before: `Results: 11 total, 10 passed, 1 failed` (suite truncated by the abort)
  - after: `Results: 13 total, 13 passed, 0 failed`
- `test/01_unit/browser_engine/html_tree_builder_spec.spl` —
  `Results: 26 total, 26 passed, 0 failed`. The file declares exactly 26 `it`
  blocks and is git-pristine, so this is a complete green run with nothing
  truncated. A pre-existing note predicted "29/29" for this spec; that figure
  was stale — 29 examples do not exist in the file.

### Unrelated, pre-existing red

`test/03_system/gui/web_showcase_full_gpu_offload_spec.spl` reports
**13 total, 5 passed, 8 failed both before and after** this change. Those 8
failures are pre-existing and unrelated: in both the fixed run and a
pristine-code control run, all 8 fail with
`Execution limit of 10000000 operations exceeded` (verified by counting that
string in both logs — 8 in each). Recording it as "unchanged and already red"
rather than as a clean number, because an earlier draft of this report
incorrectly claimed 13/13 for it.

## Provenance of these results

Measured in the shared working copy, whose HEAD is roughly 61 commits behind
`main@origin`. The origin tip does **not** currently compile: `0ae43f73ac9`
renamed `translate_call` to `translate_call_at` in `impl MirTextCodegen for
MirToLlvm` without updating the trait declaration
(`src/compiler/70.backend/backend/common/mir_text_codegen.spl:31`), filed
separately at
`doc/08_tracking/bug/mir_to_llvm_translate_call_trait_break_2026-08-04.md`.
The stale working copy still has the pre-rename compiler, which is why these
runs execute at all. These gates were therefore verified against that stale
tree, **not** against the origin tip. The serializer change is a pure `.spl`
library change that the compiler break does not interact with, but the
distinction is recorded here rather than glossed.
