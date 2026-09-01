# SPL-doctest `parse: Unexpected token` class — 13 real doc defects, 1 harness artifact

- **Filed:** 2026-08-24
- **Status:** FIXED 2026-08-25 — all 13 real defects repaired. Verified suite-wide: `Unexpected token` now occurs exactly ONCE in a full 158-file run, and that one is the category-G harness artifact, deliberately untouched.
- **Engine for every measurement below:** the Rust seed, `bin/simple`
  (`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
  60650360 bytes, 2026-08-23 04:47), run from a worktree at base `d2d0bec2e40`.

## Scope

The 2026-08-24 whole-suite class map counted 12 occurrences of
`error: compile failed: parse: in "F": Unexpected token: expected ...`. Re-swept
across all 92 failing files after the `rt_test_it` class was fixed
(`227049b0c45`), the count is **14** — two were previously masked by the
`rt_test_it` semantic error aborting the same file earlier.

This is a SEPARATE class from `parse: in "F": function arguments: ...`
(6 occurrences in the same sweep), which was already proven fictional in
`6c178bf4a30` and is not re-litigated here.

## Method (the discriminating test)

A sibling parse class died on the harness `.trim()`ing doc-comment bodies, so no
example was blamed without first proving the harness was faithful:

1. The extractor's own output was dumped via the exported `extract_doctests` and
   compared byte-for-byte (`cat -A`) against the source doc block. For
   `src/compiler/15.blocks/blocks/mod.spl:43` the extracted text matches the
   source exactly, indentation included — **extraction is faithful**, so the
   `6c178bf4a30` failure mode is not present.
2. Each of the 14 blocks was then written to a standalone `.spl` and run.
   Parsing is context-free, so a block that fails identically standalone is a
   real defect in the example; a block that parses standalone but fails inside
   the composite indicts composite CONSTRUCTION.

Result: **13 of 14 reproduce the same parse error standalone (real). 1 does
not (harness artifact).**

## Taxonomy

### A. Glued fence line — 4 blocks, `src/compiler/15.blocks/blocks/builder.spl`

Lines 264, 287, 306, 345. The newline between the fence and the example's first
line was lost, so the fence line reads:

```
        ```simple.simple_parser(\text:
        ```simple.parser(\payload, ctx:
        ```simple.simple_validator(\value:
        ```simple.const_eval(\value:
```

The extractor matches `starts_with("```simple")` and discards the rest of the
fence line, so the example's first line vanishes and what remains is an orphan:

```
    parse_json(text)
)
```

Hence `Unexpected token: expected expression, found Indent` on a 2-line block.
The source docstring is genuinely corrupted (all four in one file, one shape —
consistent with an automated rewrite that dropped the newline).

**Not repaired here, deliberately.** Restoring only the newline still does not
parse (the fragment begins with a leading `.`). Adding the receiver the file's
own working example uses —

```simple
val b = BlockBuilder("json")
    .simple_parser(\text:
        parse_json(text)
    )
```

— clears the parse error but then fails
`error: semantic: method 'simple_parser' not found on type 'BlockBuilder'`,
even though `builder.spl:21`'s example chains `.raw_text()` /
`.simple_parser(...)` identically **and passes**. Those two facts contradict
each other, and the contradiction is unresolved: either the method sugar over
`blockbuilder_*` free functions is broken in a way line 21 dodges, or line 21 is
not actually being extracted. Editing the examples on top of an unresolved
contradiction would be dodging an error that may reveal a real compiler bug.

### B. Trait-implementation syntax — 3 blocks

- `src/compiler/15.blocks/blocks/definition.spl:22`
- `src/compiler/15.blocks/blocks/mod.spl:43`
- `src/compiler/15.blocks/blocks/mod.spl:138`

All use `struct MyBlockDef: BlockDefinition:` and fail with
`Unexpected token: expected Newline, found Identifier { name: "BlockDefinition", pattern: TypeName }`.
`BlockDefinition` is declared `trait BlockDefinition:` at `definition.spl:15`, so
the examples intend a trait impl, but the parser rejects this form. Whether the
documented syntax was never valid or the parser regressed is a language question
that is not settled here.

### C. Block-literal requiring a registered block — 2 blocks

`blocks/mod.spl:18` and `blocks/easy.spl:30` end with `heredoc{ text here }` /
equivalent and fail `expected expression, found RBrace`. A custom block literal
is only lexable once its block is registered at compile time, which a doctest
composite cannot arrange. These examples are illustrative, not executable.

### D. Unterminated string literal — 2 blocks

- `src/compiler/10.frontend/core/interpreter/mod.spl:78` — `Error("Unterminated f-string")`
- `src/compiler/15.blocks/blocks/text_transforms.spl:54` — `Error("Unterminated raw string")`

Both reproduce standalone. The doc block genuinely contains an unbalanced
string delimiter.

### E. Truncated block — 1 block

`src/compiler/15.blocks/blocks/unified_registry.spl:30` —
`expected Indent, found Eof`: the example opens a suite and ends before its body.

### F. Dangling `else` — 1 block

`src/lib/nogc_async_mut/http_server/static_file.spl:63` —
`expected Indent, found Else`.

### G. HARNESS ARTIFACT — 1 block

`src/lib/nogc_async_mut/async_host/__init__.spl:92`.

- Standalone: **parses**, fails later with `error: semantic: variable 'JoinSet' not found`.
- In the composite: `Unexpected token: expected expression, found Dedent`.

Same binary, same block text. Since parsing is context-free, the break is in
`build_spl_doctest_code`'s join of `source_content` + `use std.spec.*` + block —
this block is the last thing in the file and ends on a dedent chain
(`match` / `case nil:` / `break`). This is the only one of the 14 that is not a
defect in the documented example.

Follow-up is blocked: re-verification currently cannot run at all, see below.

## Why no example was edited

Per the repo rule, a failing test is not made to pass by weakening it, and an
example is not edited to dodge an error that may reveal a real compiler or
runtime bug. Categories A and B both sit on unresolved language questions; C is
a genuine limitation of running block literals in a composite. Thirteen example
edits that would still not go green would satisfy nothing. They are recorded
here instead.

## Blocker: the doctest runner currently aborts on `main`

Measured 2026-08-24 at clean `origin/main` (`16383395b5a`), with no local
changes applied:

```
=== Running SPL Doctests ===
SPL Doctest: Running doctests from 1 source file(s)...
error[E1002]: function `unsafe` not found
  = help: check the function name or import the module that defines it
```

Exit 1, and **no `SPL Doctest: N passed, N failed` verdict line at all** — the
runner dies before executing any block, so any run over this tip is UNKNOWN, not
a pass. This reproduces without the `rt_test_it` fix applied, so it is not from
that change; it appeared with a landing in the same window as the value-bound
`unsafe` parser work. Every measurement in this record was therefore taken at
base `d2d0bec2e40`, before that tip. The taxonomy above cannot be re-measured
until this abort is fixed.

## Related

- `doc/08_tracking/bug/seed_stdlib_resolves_build_time_repo_root_before_cwd_2026-08-24.md`
  — the cross-worktree stdlib resolution defect found in the same investigation.
  Every doctest reason recorded before that was fixed had to be re-measured,
  because reasons could come from a foreign worktree's stdlib.

## Resolution 2026-08-25

All 13 real defects are repaired. Every fix was gated on the same discipline the
triage used: the block was hand-built standalone and confirmed to fail with the
recorded error BEFORE any edit, and the replacement form was confirmed to parse
standalone before it was applied. Engine: the Rust seed.

The two unresolved questions the triage stopped on both resolved as
**documentation defects, not compiler defects**, on direct measurement:

### A. Glued fence x4 — `builder.spl` 264, 287, 306, 345

Fence line and receiver both restored (triple-backtick `simple` fence +
`BlockBuilder("...")`).

**The triage's contradiction did not exist, and the first explanation offered
for it was wrong.** An earlier revision of this section claimed the
contradiction was a scope artifact — that `.simple_parser()` is sugar over the
file-scope free functions `blockbuilder_simple_parser(...)`, invisible to a
standalone probe but in scope in the composite. That was a HYPOTHESIS recorded
before it was measured, and measurement refutes it. Retracted.

What the harness actually reports, measured on a rebuilt seed that produces real
verdict lines (see "Harness" below):

```
  FAIL  src/compiler/15.blocks/blocks/builder.spl (0 passed, 5 failed, 638ms)
        Line 21:  --> .../15.blocks/blocks/modes.spl:6:1
        Line 264: --> .../15.blocks/blocks/modes.spl:6:1
        Line 288: --> .../15.blocks/blocks/modes.spl:6:1
        Line 308: --> .../15.blocks/blocks/modes.spl:6:1
        Line 348: --> .../15.blocks/blocks/modes.spl:6:1
```

Line 21 **is extracted** and **does not pass** — it fails with the same reason as
every other block in the file, and it failed identically BEFORE any edit in this
change (measured at `HEAD~1` with the same binary: `0 passed, 5 failed`). So the
triage's premise ("line 21 chains identically and passes") was simply false, and
neither of the two rival explanations it proposed was needed.

The four glued fences were still real, independent defects: the fence text was
objectively corrupted and each block reproduced its parse error standalone.
Repairing them removed every `Unexpected token` from the file. They do not turn
green, because all five blocks — the four repaired and the one untouched — are
blocked by a separate composite-only defect at `modes.spl:6:1`, filed separately.

### B. Trait-implementation syntax — 3 blocks

- `src/compiler/15.blocks/blocks/definition.spl:22`
- `src/compiler/15.blocks/blocks/mod.spl:43`
- `src/compiler/15.blocks/blocks/mod.spl:138`

All use `struct MyBlockDef: BlockDefinition:` and fail with
`Unexpected token: expected Newline, found Identifier { name: "BlockDefinition", pattern: TypeName }`.
`BlockDefinition` is declared `trait BlockDefinition:` at `definition.spl:15`, so
the examples intend a trait impl, but the parser rejects this form. Whether the
documented syntax was never valid or the parser regressed is a language question
that is not settled here.

### C. Block-literal requiring a registered block — 2 blocks

`blocks/mod.spl:18` and `blocks/easy.spl:30` end with `heredoc{ text here }` /
equivalent and fail `expected expression, found RBrace`. A custom block literal
is only lexable once its block is registered at compile time, which a doctest
composite cannot arrange. These examples are illustrative, not executable.

### D. Unterminated string literal — 2 blocks

- `src/compiler/10.frontend/core/interpreter/mod.spl:78` — `Error("Unterminated f-string")`
- `src/compiler/15.blocks/blocks/text_transforms.spl:54` — `Error("Unterminated raw string")`

Both reproduce standalone. The doc block genuinely contains an unbalanced
string delimiter.

### E. Truncated block — 1 block

`src/compiler/15.blocks/blocks/unified_registry.spl:30` —
`expected Indent, found Eof`: the example opens a suite and ends before its body.

### F. Dangling `else` — 1 block

`src/lib/nogc_async_mut/http_server/static_file.spl:63` —
`expected Indent, found Else`.

### G. HARNESS ARTIFACT — 1 block

`src/lib/nogc_async_mut/async_host/__init__.spl:92`.

- Standalone: **parses**, fails later with `error: semantic: variable 'JoinSet' not found`.
- In the composite: `Unexpected token: expected expression, found Dedent`.

Same binary, same block text. Since parsing is context-free, the break is in
`build_spl_doctest_code`'s join of `source_content` + `use std.spec.*` + block —
this block is the last thing in the file and ends on a dedent chain
(`match` / `case nil:` / `break`). This is the only one of the 14 that is not a
defect in the documented example.

Follow-up is blocked: re-verification currently cannot run at all, see below.

## Why no example was edited

Per the repo rule, a failing test is not made to pass by weakening it, and an
example is not edited to dodge an error that may reveal a real compiler or
runtime bug. Categories A and B both sit on unresolved language questions; C is
a genuine limitation of running block literals in a composite. Thirteen example
edits that would still not go green would satisfy nothing. They are recorded
here instead.

## Blocker: the doctest runner currently aborts on `main`

Measured 2026-08-24 at clean `origin/main` (`16383395b5a`), with no local
changes applied:

```
=== Running SPL Doctests ===
SPL Doctest: Running doctests from 1 source file(s)...
error[E1002]: function `unsafe` not found
  = help: check the function name or import the module that defines it
```

Exit 1, and **no `SPL Doctest: N passed, N failed` verdict line at all** — the
runner dies before executing any block, so any run over this tip is UNKNOWN, not
a pass. This reproduces without the `rt_test_it` fix applied, so it is not from
that change; it appeared with a landing in the same window as the value-bound
`unsafe` parser work. Every measurement in this record was therefore taken at
base `d2d0bec2e40`, before that tip. The taxonomy above cannot be re-measured
until this abort is fixed.

## Related

- `doc/08_tracking/bug/seed_stdlib_resolves_build_time_repo_root_before_cwd_2026-08-24.md`
  — the cross-worktree stdlib resolution defect found in the same investigation.
  Every doctest reason recorded before that was fixed had to be re-measured,
  because reasons could come from a foreign worktree's stdlib.

## Resolution 2026-08-25

All 13 real defects are repaired. Every fix was gated on the same discipline the
triage used: the block was hand-built standalone and confirmed to fail with the
recorded error BEFORE any edit, and the replacement form was confirmed to parse
standalone before it was applied. Engine: the Rust seed.

The two unresolved questions the triage stopped on both resolved as
**documentation defects, not compiler defects**, on direct measurement:

### A. Glued fence x4 — `builder.spl` 264, 287, 306, 345

Fence line and receiver both restored (triple-backtick `simple` fence + `BlockBuilder("...")`),
matching the file's own working line-21 example.

The triage's contradiction — repairing the fence yields `method simple_parser
not found on type BlockBuilder` while line 21 chains identically and passes —
is explained by **harness context, not a compiler bug**. `.simple_parser()` is
method sugar over the free functions `blockbuilder_simple_parser(self:
BlockBuilder, ...)` declared at file scope in `builder.spl`. The triage's probe
was a hand-built STANDALONE file, where those free functions are not in scope,
so the sugar cannot resolve. The doctest composite prepends `source_content`,
which puts them in scope — which is exactly why line 21 passes there. The two
facts never actually contradicted each other; they were measured in two
different scopes.

### B. Trait-implementation syntax x3 — `definition.spl:22`, `mod.spl:43`, `mod.spl:138`

`struct X: Trait:` has **zero** occurrences in the entire tree
(`grep -rn "^struct [A-Za-z_]*: [A-Z]" src/ --include=*.spl` -> 0). The live,
working convention is `struct X:` plus a separate `impl Trait for X:`, used at
`tls/transport.spl:38`, `web_ui/plugin.spl:87` and elsewhere. A minimal fixture
confirms it: `impl Greeter for Hi:` runs exit 0, while `struct Hi: Greeter:`
fails with the recorded error verbatim
(`expected Newline, found Identifier { name: "Greeter", pattern: TypeName }`).
The examples documented a form that never existed — not a parser regression.
Rewritten to the working form.

### C. Block literal x2 — `mod.spl:18`, `easy.spl:30`

A custom block literal is only lexable in a compilation unit where the block is
already registered at COMPILE time, so it cannot appear in the same example that
registers it at RUNTIME. This is a language property, not a defect. The usage is
now expressed as a comment — which is the convention the same file's Tier-3
example (`mod.spl:138`) already used for exactly this reason. Nothing was
retagged or removed from the doctest population; the extractor has no
ignore/no_run tag, and using one would have been a skip.

### D/E/F — 4 blocks, unambiguous

- `interpreter/mod.spl:78` and `text_transforms.spl:54` used **Python** string
  syntax. Measured: `"""..."""` is valid Simple multiline (exit 0), a bare
  multi-line `"` is not, and `'''...'''` is not Simple at all. `interpreter`
  took `"""`; `text_transforms` could not (its example sits inside a `"""`
  docstring, which `"""` would terminate early) so it took the escaped
  single-line form, verified exit 0.
- `unified_registry.spl:30` and `static_file.spl:63` had an indented block whose
  only body was a comment. A comment is not a statement in Simple, exactly as in
  Python; minimal fixtures reproduce `expected Indent, found Eof` and
  `expected Indent, found Else` verbatim. Each branch was given a real statement.

### Not touched

`async_host/__init__.spl:92` — the harness artifact. Unchanged, as recorded.

## Harness

The triage could not re-measure because the runner aborted with
``error[E1002]: function `unsafe` not found`` and emitted no verdict line. That
abort was root-caused (not worked around) as a **binary/source skew**: the
deployed seed was built 2026-08-23, before the parser learned the value-bound
`unsafe(capabilities: [...])` form, while `io_runtime.spl` had since adopted it
(`7ef30bafe0e`). Rebuilding the seed from the tree's own `src/compiler_rust`
fixes it at root. See
`doc/08_tracking/bug/deployed_seed_cannot_parse_value_bound_unsafe_2026-08-25.md`.

**Engine for every "Resolution" measurement:** a seed rebuilt from this tree,
**60634072 bytes, 2026-08-25 05:17**, deployed into the measuring lane only.
Smoke-verified before use: `std.io_runtime.time_now_unix_micros` (the value-bound
`unsafe` path) exits 0, and a single-file doctest emits a real verdict line.

## Measured result

Per-file, **same binary on both sides**, before = `HEAD~1`, after = `HEAD`:

| file | before | after |
|---|---|---|
| `10.frontend/core/interpreter/mod.spl` | 1 passed, 3 failed | 1 passed, 2 failed |
| `15.blocks/blocks/builder.spl` | 0 passed, 5 failed | 0 passed, 5 failed |
| `15.blocks/blocks/definition.spl` | 1 passed, 1 failed | **2 passed, 0 failed** |
| `15.blocks/blocks/easy.spl` | 2 passed, 1 failed | 2 passed, 1 failed |
| `15.blocks/blocks/mod.spl` | 0 passed, 6 failed | 0 passed, 6 failed |
| `15.blocks/blocks/text_transforms.spl` | 0 passed, 2 failed | 1 passed, 1 failed |
| `15.blocks/blocks/unified_registry.spl` | 0 passed, 1 failed | 0 passed, 1 failed |
| `nogc_async_mut/http_server/static_file.spl` | 0 passed, 2 failed | 1 passed, 1 failed |
| **total** | **4 passed, 21 failed** | **7 passed, 17 failed** |

The headline number understates the change, because the `Unexpected token` class
is fully eliminated even where the block does not go green. `blocks/mod.spl` is
the clearest evidence — same 6 blocks before and after, and every parse error is
gone:

```
BEFORE  Line 18:  ... Unexpected token: expected expression, found RBrace
        Line 43:  ... Unexpected token: expected Newline, found Identifier { name: "BlockDefinition" }
        Line 138: ... Unexpected token: expected Newline, found Identifier { name: "BlockDefinition" }
        Line 33/120/128: --> modes.spl:6:1
AFTER   Line 18/35/45/125/133/143: --> modes.spl:6:1   (all six, no parse errors)
```

**Why 10 blocks still fail — two separate defects, neither a doc defect:**

1. **`modes.spl:6:1` composite-only failure** — blocks all of `builder.spl` (5),
   `blocks/mod.spl` (6), `unified_registry.spl` (1) and `easy.spl` (1). The line
   is `export use compiler.frontend.block_types.*`, a wildcard re-export.
   Importing that module standalone succeeds (`use compiler.blocks.modes.{LexerMode}`
   -> exit 0), so the failure exists only inside the doctest composite built by
   `build_spl_doctest_code` (`doctest_runner.spl:440-441`). This is the same
   family as the category-G harness artifact, and it affects blocks nobody
   edited. Filed separately.
2. **Placeholder identifiers** — some repaired examples reference helpers that
   were never defined (`my_parser`, `parse_json`, `parse_sql`). Those land in the
   `variable X not found` class (33 occurrences suite-wide), which is a different
   class from this one and is not re-litigated here.

## Whole-suite verdict — CONFIRMED

A whole-suite run initially aborted with no verdict line, three separate times.
All three aborts were root-caused and cleared (none was a doctest defect):

1. deployed seed predated the value-bound `unsafe` parser support -> rebuilt.
2. `easy_fix/accessor_rewrite.spl` used the reserved word `unsafe` as a local
   variable, so the file had never parsed. Renamed.
3. `90.tools/lint/_LintMain/entry_and_fixes.spl` used the reserved word
   `generic` the same way. Renamed.

With those cleared the suite reaches a verdict:

```
SPL Doctest: Running doctests from 158 source file(s)...
SPL Doctest: 295 passed, 186 failed, 0 skipped
```

(exit 1, as expected while 186 doctests still fail.)

**The class this record tracks is gone.** `Unexpected token` occurs exactly
**once** in that whole-suite output, down from the 14 the triage counted:

```
spl_doctest_src_lib_nogc_async_mut_async_host___init___spl_92.spl":
Unexpected token: expected expression, found Dedent
```

That is category G — the harness artifact, deliberately not edited. All 13 real
defects are fixed and verified absent suite-wide.

The `267 passed, 215 failed` figure quoted as a baseline for this work was taken
on the old binary that aborts, so it is NOT comparable to the number above and
is not claimed as a before/after pair. The per-file table is the controlled
measurement of this change.
