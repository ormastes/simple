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

## 2026-08-25 (later) — my "sharpest lead" was WRONG, and the residue is not a compiler defect at all

### Correction: `trim_lines` never had "opposite verdicts"

The section above presents this as the sharpest lead on the board:

> `trim_lines(lines: [text])` is a TYPED array parameter and it still fails — but
> only in context. Identical source, identical function, opposite verdicts.

**It is not the same function.** `trim_lines` is defined TWICE in this tree:

```
src/app/utils/parsing.spl:107    fn trim_lines(lines: [text]) -> [text]:   # typed
src/lib/common/text_advanced.spl:104  fn trim_lines(lines):                # UNTYPED
```

So are `normalize_indent` (`parsing.spl:169` typed / `text_advanced.spl:465`
untyped) and `dedent_lines` (`spipe_docgen/parser.spl:533` typed /
`text_advanced.spl:507` untyped).

The failing one was always `text_advanced`'s untyped copy. The `pp` build that
"passed" imported only `parsing`'s typed copy, so nothing contradicted anything.
The contradiction existed only in **my probe**, which printed
`self.builder.current_function`'s bare NAME and could not distinguish two
same-named functions in different modules.

Proof: annotating `text_advanced`'s three untyped copies — and touching nothing
else — removed exactly those three from the failure list (11 -> 8). Renaming
`parsing.trim_lines`'s parameter, tested first on the "shared parameter name"
hypothesis, changed nothing and refuted it.

**There is no closure-dependent corruption. There is no shared-registry
poisoning.** The lead was an artifact of name ambiguity in the diagnostic I built
to escape name ambiguity.

### What the residue actually is: missing type annotations, all of it

Driving the 4-line reproducer down, one annotation at a time:

| step | annotation added | reproducer |
|---|---|---|
| start | — | **11** |
| duplicate untyped copies | `trim_lines`, `dedent_lines`, `normalize_indent` in `text_advanced` | 8 |
| untyped params | `prefix_lines`, `suffix_lines`, `remove_empty_lines`, `detect_indent` (`lines: [text]`) | 4 |
| **missing RETURN type** | `fn extract_words(text: text)` -> `-> [text]` | **2** |

`extract_words` is the one that is not a parameter: it declared no return type at
all, so `val words = extract_words(text)` had nothing to inherit — which is what
was failing inside `longest_word` and `most_common_words`, both of which looked
like "a local from a split" from the outside.

Every annotation added matches the function's own docstring example
(`prefix_lines(["hello", "world"], "> ")`, `longest_word("The quick brown fox")
# ("quick", 5)`). None is a guess.

**Remaining 2:** `multi_replace` (untyped `pairs`; its element type is not
obvious from the signature, so still deliberately not guessed) and
`most_common_char` (not yet traced). A third, unrelated feature gap becomes
reachable once these clear: `unsupported array/string slice index a[start:end]`.

### Consequence for the framing

`#143` in this closure is **not a compiler defect**. It is the lowering honestly
reporting that it has no type to work with, on library code that never declared
one. The compiler-side type-loss defects in this chain were real and are fixed
(`9ca094b44ee`, `3dc5b8dd8a2`); what is left is missing annotations in
`src/lib/common/text_advanced.spl`.

### Not landed

The annotations are measured (11 -> 2) but NOT landed. `text_advanced.spl` is
widely imported, and the bar this lane has held — fixture differential, a
native-build corpus, AND a check that the corpus actually enters the changed
path — was not run for them. The next lane starts from a measured 11 -> 2 and a
one-line diff per function.

### A pattern worth naming

This is the fourth bare-name ambiguity to cause a wrong answer in this session:
the parser's `arm_body` local shadowing another module's global (`ec272de6947`),
a name-only lookup discarding qualifiers in `resolve_name_variants` (sibling
lane), duplicate function names across modules here, and — the one worth
admitting — **my own diagnostic**, which printed a bare function name and
manufactured a false contradiction from it. Shared state and diagnostics keyed by
bare name are a systemic habit in this compiler, and tooling built to investigate
it inherits the same flaw unless it prints a qualifier.

## 2026-08-25 (later) — annotations LANDED, with the differential

The eight annotations measured above are now landed in
`src/lib/common/text_advanced.spl`. Each matches the function's own docstring
example; none is a guess:

| function | added | docstring evidence |
|---|---|---|
| `extract_words` | `-> [text]` | `extract_words("Hello, world! 123")  # ["Hello", "world", "123"]` |
| `trim_lines` | `lines: [text]) -> [text]` | `trim_lines(["  hello  ", "  world  "])  # ["hello", "world"]` |
| `remove_empty_lines` | `lines: [text]) -> [text]` | `# ["hello", "world"]` |
| `prefix_lines` | `lines: [text]) -> [text]` | `# ["> hello", "> world"]` |
| `suffix_lines` | `lines: [text]) -> [text]` | `# ["hello!", "world!"]` |
| `detect_indent` | `lines: [text]` | `detect_indent(["hello", "  world", "    foo"])  # 2` |
| `dedent_lines` | `lines: [text]` | `# ["hello", "  world"]` |
| `normalize_indent` | `lines: [text]` | `# ["    hello", "        world"]` |

`multi_replace` (untyped `pairs`) and `most_common_char` remain untouched — the
element type is not derivable from the signature and `most_common_char` was never
traced. Not guessed, for the third time.

### Behavioural verification: identical, and correct against every docstring

Native execution of these functions is **impossible on either tree**, so that
route was closed (see the limitation below). The interpreter path is not, and it
exercises the real functions:

```
        BASE (origin/main)          ANNOTATED
trim    |hello|world                |hello|world
rmempty |hello|world                |hello|world
prefix  |> hello|> world            |> hello|> world
suffix  |hello!|world!              |hello!|world!
detect  2                           2
dedent  |hello|  world              |hello|  world
norm    |    hello|        world    |    hello|        world
words   |Hello|world|123            |Hello|world|123
```

Byte-identical between trees, and every line matches the documented example. All
eight annotated functions are covered — this is behaviour, not a site count.

### Site counts, same method on both trees

| build | base | annotated |
|---|---|---|
| 4-line reproducer | **11** | **2** |
| `native-build src/app/mcp/main.spl` | **16** | **7** |

No new error kinds appear in either; the remaining rows are the same `#143`
message.

### Entry check first, before quoting any differential

The 16-program native-build corpus used for `9ca094b44ee` and `3dc5b8dd8a2` was
checked for whether it compiles `text_advanced` **before** being run for this
change. It does not — zero occurrences in its build logs. Quoting a
byte-identical result from it would have been the third false green in this
lane's favour, so it is not quoted. The MCP build is the corpus that actually
exercises this module, and it is reported above.

### Limitation, stated rather than worked around

**No native binary is obtainable from `text_advanced` on EITHER tree.** Importing
it pulls slice-using functions and MIR lowering stops at
`unsupported array/string slice index a[start:end] (no native array-slice
lowering)`. On the base tree the same import stops earlier, at
`unsupported MIR type kind [infer-arm]: HirTypeKind::Infer` — the untyped
parameters. So the annotations demonstrably move the failure from the untyped-
parameter gap to an unrelated, pre-existing feature gap, but they cannot be
verified by native execution. The interpreter comparison above is what stands in
its place.

That slice gap is now the next thing behind `#143` for this module.
