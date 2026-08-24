# SPL-doctest `parse: Unexpected token` class — 13 real doc defects, 1 harness artifact

- **Filed:** 2026-08-24
- **Status:** OPEN (recorded, deliberately NOT "fixed" by editing examples — see
  "Why no example was edited")
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
