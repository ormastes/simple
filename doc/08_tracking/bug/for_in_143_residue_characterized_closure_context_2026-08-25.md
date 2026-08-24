# The #143 residue is characterized: names, a 4-line reproducer, and one measured cause (2026-08-25)

- **Status:** OPEN — characterized, not fixed
- **Severity:** MEDIUM — it is the largest remaining `#143` block on the MCP
  native-build, and it was previously "uncharacterized"
- **Area:** `50.mir` for-in lowering; trigger is import-closure context
- **Found by:** continuing
  `for_in_optional_initialized_local_loses_collection_type_2026-08-24.md` after
  the optional-payload fix (`3dc5b8dd8a2`) did NOT clear these

## They now have names

The `#143` diagnostic carries no usable span (see
`for_in_143_diagnostic_span_cannot_localize_the_loop_2026-08-24.md`), so the 15
sites were anonymous. `self.builder.current_function` is available at the error
site and names every one of them in a single run:

| function | file | iterated expression |
|---|---|---|
| `prefix_lines` | `src/lib/common/text_advanced.spl:145` | **untyped param** `lines` |
| `suffix_lines` | `text_advanced.spl:157` | **untyped param** `lines` |
| `remove_empty_lines` | `text_advanced.spl:115` | **untyped param** `lines` |
| `detect_indent` | `text_advanced.spl:441` | **untyped param** `lines` |
| `multi_replace` | `text_advanced.spl:1279` | **untyped param** `pairs` |
| `most_common_words` | `text_advanced.spl:383` | local from `split` |
| `longest_word` | `text_advanced.spl:306` | local from `split` |
| `most_common_char` | `text_advanced.spl:361` | local from `split` |
| `normalize_indent` | `src/app/utils/parsing.spl:169` | local from `split` |
| `trim_lines` | `src/app/utils/parsing.spl:107` | **typed param `[text]`** |
| `dedent_lines` | `src/app/spipe_docgen/spipe_docgen/parser.spl:533` | **typed param `[text]`** |
| `json_array_flatten` | `src/lib/common/json/array_ops.spl:456` | `val list = json_to_array(arr)` (`-> any?`) |
| `_mcp_probe_manifest_hash` | `src/app/mcp/main_static_tools.spl:315` | `for ch in name` over a `text` field |
| `handle_assistant_list_tasks` x2 | `src/app/mcp/main_lazy_assistant.spl:20` | `Field` receiver — the hole `fb7e76c489a` left open |

## A 4-line reproducer replaces the 61-module build

```
use std.common.text_advanced.{prefix_lines}

fn main() -> i64:
    print("ok")
    return 0
```

reproduces **11 of the 15**. Anyone working on this no longer needs an MCP build.

## One cause is now measured, and it is genuine missing type information

Four of the five untyped parameters were annotated as an experiment
(`lines: [text]`, matching each function's own docstring example — e.g.
`prefix_lines(["hello", "world"], "> ")`). The reproducer went **11 -> 7**, and
exactly the four annotated functions disappeared from the list. So for those,
the cause is simply that the parameter carries no type and the lowering has
nothing to work with. `multi_replace`'s `pairs` was deliberately left alone: its
element type is not obvious from the signature, and annotating on a guess is the
failure mode this lane has already refused once.

**The annotations were NOT landed.** They are a stdlib edit to a widely imported
module and would need the differential discipline used for `9ca094b44ee` /
`3dc5b8dd8a2` (fixture set + native-build corpus + a check that the corpus
actually enters the changed path), which was not run. The experiment is recorded
so the next lane starts from a measured 11->7 rather than a hypothesis.

## The sharpest remaining lead: same function, different closure, different result

`trim_lines(lines: [text])` is a TYPED array parameter and it still fails — but
only in context:

| build | `trim_lines` |
|---|---|
| `use app.utils.parsing.{trim_lines}` (its own module is the target) | **0 sites — builds clean** |
| `use std.common.text_advanced.{prefix_lines}` (reached through that closure) | **fails** |

Identical source, identical function, opposite verdicts. Whatever the trigger is,
it is a property of the import closure, not of the statement or the signature.
That is the same shape as the parser-local/global collision earlier in this
chain (`ec272de6947`), where a *different module's* declaration corrupted shared
state — worth checking for a shared registry poisoned during lowering.

## Shapes that are NOT the cause (each tested, each builds and runs)

Every reduction of the remaining shapes builds cleanly in isolation, which is why
they looked uncharacterizable before the names existed:

| shape | result |
|---|---|
| `fn f(lines: [text])` + `for line in lines` | builds, runs `n=5` |
| same, across a module boundary | builds, runs `n=5` |
| `fn f(t: text)` + `val lines = t.split(",")` + `for l in lines` | builds, runs `n=5` |
| `for ch in <text field>` via `tools[i].name` | builds, runs `n=3` |
| `fn f(lines)` — untyped param | **FAILS** (this is the measured cause above) |

## NOT verified

- The contextual trigger itself is still unknown. Only its shape is pinned:
  closure-dependent, not statement- or signature-dependent.
- The four annotations are measured (11 -> 7) but unlanded and unvalidated
  beyond that count.
- `json_array_flatten` is the `-> any?` case: correctly unfixable by type
  preservation, since `any` carries no container type (see `3dc5b8dd8a2`).
- MCP still produces no binary, and clearing `#143` entirely would still not be
  enough: `borrow_check()` runs after `lower_to_mir`, so the NLL false positive
  in `nll_mut_borrow_of_local_false_positive_at_return_2026-08-24.md` has never
  executed on this closure. When `#143` does clear, that becomes the frontier,
  and it is a project rather than a patch —
  `LivenessAnalysis.record_use`/`record_def` have no callers at all.
