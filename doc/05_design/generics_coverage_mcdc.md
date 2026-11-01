<!-- lane: generics-coverage-mcdc / MC/DC tooling sub-lane -->
# MC/DC Module Coverage for Compiler Sources — Detail Design

Status: implemented (pure Simple), 2026-11-01. Owner lane: `generics-coverage-mcdc`.

## 1. Problem

`scripts/check/cert/mcdc_instrument.spl` instruments one standalone program
(`if`/`elif`/`while` headers only, atoms without parentheses or calls, report
printed by a wrapped `main`). `std.mcdc` (`src/lib/nogc_sync_mut/mcdc.spl`)
provides `register_decision` / `record_evaluation` / `analyze_mcdc` for code
that calls it by hand. Neither can answer "what CD / MC/DC coverage do the
specs under `test/01_unit/compiler/` give `src/compiler/30.types/type_infer/
generic_calls.spl`?", because the module under test is loaded by the
interpreter through `use compiler.types.type_infer.generic_calls`, not run as
a program, and its decisions use calls, parenthesized sub-expressions, boolean
chains in `return`/`val` positions and match guards.

The interpreter also has an internal MC/DC lane (`eval_control_condition`,
`rt_mcdc_record_vector_v1`, obligation manifests carried by the test runner).
That lane needs probe emission from the binary in use; the Rust seed reports
"MC/DC mode degraded". The tool below is binary-agnostic: it only needs a
runtime that resolves modules through `SIMPLE_LIB` and can run specs.

## 2. Requirements (traceability ids used by the specs)

| id | requirement |
|----|-------------|
| REQ-MCDC-MOD-001 | Paren/call-aware tokenizer with byte offsets; strings, comments, numbers with suffixes, two-char operators, bracket matching |
| REQ-MCDC-MOD-002 | Decisions = `if`/`elif`/`while` headers, `if` expressions, `case … if g:` guards, and any `and`/`or` chain elsewhere (return, val/var, call args, nested groups); conditions = leaf operands including calls and non-boolean paren groups; rewrite preserves short-circuit semantics and physical line count |
| REQ-MCDC-MOD-003 | CD coverage per decision: both outcomes and every condition observed true and false |
| REQ-MCDC-MOD-004 | MC/DC per condition: independence pair under unique-cause, else masking (sibling-subtree rule); single-condition decisions covered by both outcomes; uncovered reasons with file:line |
| REQ-MCDC-MOD-005 | Runtime recorder: LIFO frames, re-entrant, masked conditions never probed, one SDN row per distinct vector, no at-exit hook needed |
| REQ-MCDC-MOD-006 | SDN manifest/record tables, de-numbered shadow paths mirroring the loader's `SIMPLE_LIB` probe |

## 3. Components

```
src/lib/nogc_sync_mut/mcdc/
  module_tokenizer.spl   mcdc_tokenize_line, mcdc_tok_match, mcdc_line_depth_delta
  module_decisions.spl   McdcDecisionInfo/McdcCondition/McdcTreeNode,
                         mcdc_parse_decision_expr, mcdc_rewrite_logical_line,
                         mcdc_instrument_source, tree <-> postfix
  module_probe.spl       mcdc_mod_begin / mcdc_mod_probe / mcdc_mod_commit (runtime)
  module_analyzer.spl    McdcEvalRecord, mcdc_pair_kind, mcdc_analyze_decision,
                         mcdc_summarize_file, mcdc_uncovered_reasons
  module_records.spl     SDN table codec, mcdc_shadow_rel_paths
scripts/check/cert/mcdc_module_coverage.spl   CLI: instrument | run | report
scripts/check/cert/mcdc_module_coverage.shs   thin wrapper (SIMPLE_BIN)
test/01_unit/lib/mcdc_module_{tokenizer,decisions,analyzer,probe,records}_spec.spl
```

Dependencies point downward only: CLI → records/analyzer/decisions → tokenizer.
`module_probe` depends only on `std.io_runtime` so that instrumented compiler
modules pull in nothing else.

## 4. Data structures

```
McdcTok            kind (IDENT NUMBER STRING OP LPAREN … AND OR NOT AT), text, pos, end   (byte offsets)
McdcCondition      index, expr (verbatim source), line, col
McdcTreeNode       kind (LEAF NOT AND OR), cond, left, right      (flat array, root index kept)
McdcDecisionInfo   id (global in the run), file, line, col, kind (if|elif|while|guard|if_expr|expr),
                   expr, conditions[], nodes[], root
McdcEvalRecord     decision, values (bit k = condition k true), evaluated (bit k = probed), outcome
McdcPair           kind (0 none | 1 unique-cause | 2 masking), a, b   (indices into the decision's vectors)
McdcConditionCoverage / McdcDecisionCoverage / McdcFileSummary   (report rows)
```

Condition ordinals are source order (left to right); bits are `1 << k`, so a
decision may have at most 62 conditions (larger ones are skipped and listed in
`skipped.sdn`).

## 5. Tokenizer

Owns a small lexer rather than reusing `compiler.frontend.core.lexer`: that
lexer is a global-state stream with indentation tracking and AST-module
dependencies and emits no byte spans, while the rewrite must rebuild the line
byte-exactly around the spans it replaces. Character classes match
`compiler.frontend.core.lexer_chars`. Handles `"…"`, `'…'`, `"""…"""` on one
logical line, `r"`/`b"`/`f"` prefixes, `#` comments, numbers with suffixes and
`..` ranges, the two-char operators, and `::`. All offsets are byte offsets
(consistent with `text.len()`, `byte_at`, `slice`).

## 6. Decision extraction and rewrite

### 6.1 Logical lines

Physical lines are joined while bracket depth stays positive (max 64 lines);
docstring regions (`"""` toggling) are copied verbatim; lines that do not
tokenize (unterminated string) are copied verbatim and listed as skipped.

### 6.2 Segmentation

Within a token range, **boundary tokens** split the range into segments:
`,` `:` assignment operators (`=` `+=` … `->` `=>`) and the keywords
`if elif while else return val var for match case fn me pub use import yield
assert with where export extern static` (`in` only after `for`). Bracket
groups are opaque to the splitter and recursed into separately, so nested
decisions inside call arguments are found (`f(p or q)`).

A segment is a decision when
* it follows `if`/`elif`/`while` and is terminated by `:` (header; a single
  condition counts; `if val x = …:` pattern bindings are never matched because
  `val` is itself a boundary), kind = `if` (line start), `guard` (line starts
  with `case`), `if_expr` (elsewhere), `elif`, `while`; or
* it contains a top-level `and`/`or` (kind `expr`).

Lines whose first token is `@` are left verbatim (attributes such as
`@cfg(a or b)` are not runtime decisions).

### 6.3 Tree

`or := and ("or" and)*`, `and := not ("and" not)*`, `not := "not" not | primary`,
`primary := "(" or ")"` only when the group is a whole operand, contains a
boolean operator and no boundary token; otherwise a **leaf** = all tokens up
to the next `and`/`or` at this depth (`(x + y) > 2`, `f(a, b) == 3`,
`x not in y`). A parse failure leaves the segment untouched and records a
skip reason.

### 6.4 Rewrite

```
E                      ->  mcdc_mod_commit(ID, mcdc_mod_begin(ID) and (E'))
leaf k                 ->  mcdc_mod_probe(ID, k, (leaf text))
not X / X and Y / X or Y   keep operators; binary children parenthesized
```
`begin` returns true, so `begin(ID) and (E')` evaluates `E'` with the original
operators and the original left-to-right short-circuit; a probe runs only
after its operand was evaluated, so skipped operands are never probed (masked).
Gaps between tokens are copied from the source except inside the regenerated
operator skeleton; newlines lost there are padded at the end of the logical
line so physical line numbers downstream stay unchanged. Exactly one line is
injected (`use std.nogc_sync_mut.mcdc.module_probe.{…}`, before the first
top-level `use`); manifest lines are the ORIGINAL line numbers, and
`McdcInstrumentResult.use_line` records where the shift of +1 begins.

## 7. Runtime recorder (`module_probe`)

Global frame stack `(decision, values, evaluated)`:

* `begin(d)` pushes an empty frame.
* `probe(d, k, v)` sets `evaluated |= 1<<k` and `values |= v<<k` on the top
  frame; returns `v` unchanged. Nested decisions evaluated inside an operand
  are begun and committed before the enclosing probe runs, so the top frame is
  always the right one; a mismatch increments an anomaly counter instead of
  corrupting data.
* `commit(d, outcome)` pops down to the frame for `d` (discarding stale frames
  left by an early `?` return inside a condition), returns `outcome`, and
  records `(d, values, evaluated, outcome)` if that vector is new for the
  process.

Dedup makes writes proportional to distinct vectors (≤ 2^n per decision),
which is why the sink can append on first sight and needs no exit hook: the
file is complete whenever the process stops. Sink = `$SIMPLE_MCDC_RECORDS/
records.sdn`, shared by all spec processes of a run (one short append per new
vector; duplicates across processes are harmless to the analyzer; unset →
memory only). The CLI writes the header row when it creates the file.

Facade hygiene: the probe imports only `env_get_opt` and `file_append_text`,
and the CLI reads through `file_read_result` / writes through
`file_write_exact`. Those names have one definition in the tree; `file_read`,
`file_write` and `list_dir` have several co-compiled copies with differing
signatures and the seed's cross-module dispatch was observed binding
`file_read` to a copy that returned empty text (see the warning block in
`io_runtime.spl`). Using one records file also removes the need for any
directory listing.

## 8. Coverage definitions (`module_analyzer`)

Let `E` be the distinct vectors of a decision.

* **Decision outcomes**: both `true` and `false` present.
* **Condition both-valued**: condition `k` observed true and false while
  evaluated (bit set in `evaluated`).
* **CD % (file)** = (decisions with both outcomes + conditions both-valued)
  / (decisions + conditions) × 100.
* **Independence pair** for `k` = `(A, B) ∈ E²` with `A.outcome ≠ B.outcome`,
  `k` evaluated in both with different values, and
  * *unique-cause*: every other condition evaluated in both has the same
    value (a condition masked in either vector is don't-care), or
  * *masking*: for every and/or ancestor of `k`, the sibling subtree has the
    same value in `A` and `B` whenever it is evaluated in both (subtree value
    computed bottom-up with short-circuit: `-1` unevaluated, else 0/1). A
    sibling skipped by short-circuit in one vector could not have changed that
    outcome, so it is don't-care. Unique-cause pairs are masking pairs; the
    strongest kind found is reported. Example `(a and b) or c`:
    `(T,F,F)=F` / `(F,-,T)=T` is a masking pair for `c` although `a` differs.
* **MC/DC % (file)** = conditions with a pair / conditions × 100. A
  one-condition decision gets its pair from any two vectors with opposite
  outcomes.
* **Uncovered list**: per decision `file:line [kind] expr`, then per condition
  `cK \`expr\`: never evaluated (masked) | only true/false; no independence
  pair | no independence pair`, and decision-level `never evaluated` /
  `outcome never true|false`.

Pair search is O(|E|² · n); `|E|` is capped at 4096 vectors per decision.

## 9. Shadow tree and run flow

```
build/coverage/mcdc/<run>/
  src/<de-numbered path>.spl     instrumented copies (SIMPLE_LIB root)
  decisions.sdn                  |id, file, line, col, kind, conditions, tree, expr|
  conditions.sdn                 |decision, index, line, col, expr|
  files.sdn                      |file, shadow, decisions, conditions|
  skipped.sdn                    |note|
  records/records.sdn            |decision, values, evaluated, outcome|   (appended by probes)
```

The interpreter resolves `use compiler.types.type_infer.generic_calls` by
probing, in order, the importing file's directory, `$SIMPLE_LIB/<dotted path>`
with the path used **verbatim** (`compiler/types/type_infer/generic_calls.spl`),
then `src/` with numbered-directory resolution
(`module_loader_resolve.spl` strategies 1–5). Therefore the shadow tree stores
`30.types` as `types`; lib files are mirrored both as `lib/<family>/…` and
`lib/…` (both `std.<family>.x` and `std.x` spellings resolve). Everything not
instrumented falls through to the real `src/`, including the probe module.

```
instrument --run R <files>   write shadow + manifest (ids global across files)
run        --run R <specs>   SIMPLE_LIB=<abs R/src> SIMPLE_MCDC_RECORDS=<abs R/records>
                             <bin> test <specs> --no-cache --mode=interpreter
report     --run R           read manifest + records/records.sdn, print table
```

`--no-cache` is mandatory: a cached spec result would not re-execute the
module. `--mode=interpreter` is the mode whose loader honours `SIMPLE_LIB`;
native/SMF test modes use the driver's own resolution and are out of scope.

### 9.1 Seed fallback: `run --in-place`

The Rust bootstrap seed's resolver
(`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`)
climbs from the importing file's directory to the project root (`src/` or
`Cargo.toml`) and never consults `SIMPLE_LIB` (the seed reads that variable
only in its memory guard). A shadow tree is therefore invisible to the seed:
measured 2026-11-01, a spec calling instrumented `lexer_chars` under
`SIMPLE_LIB=<shadow>` ran green with `rows=0 evals=0`. `run --in-place`
instead:

1. backs up each instrumented file's original to `<run>/backup/<path>`
   (skipped when a backup already exists, so a crashed run never overwrites
   a backup with instrumented text),
2. writes the instrumented copy over the real path,
3. runs the specs,
4. restores every original from backup and verifies it byte-identical,
   printing `RESTORE FAILED … copy … back by hand` otherwise.

`restore --run R` repeats step 4 after an interrupted run. In-place mode
mutates the working tree for the duration of the spec run; use it only in a
worktree you own, never in a shared checkout.

## 10. Limits

* Decisions inside string interpolation, attributes, docstrings and comments
  are not instrumented (by design).
* `x not in y`-style infix `not` stays inside a leaf (correct but coarse).
* A bare `Pat if guard:` arm without `case` is only recognized when the
  line starts with `case`; other guard spellings are left verbatim.
* Conditions with side effects are evaluated exactly once (probes wrap, they
  do not re-evaluate), but an early-return `?` inside a condition leaves a
  stale frame that the next `commit` for an outer decision discards; the
  partially built vector of the aborted decision is dropped.
* Concurrency: the frame stack is process-global; specs that evaluate
  instrumented decisions from several OS threads can interleave frames
  (anomaly counter grows). Compiler unit specs are single-threaded.
* Strongly coupled conditions (same atom twice in one decision) are two
  conditions; no coupling analysis is attempted.
* Runtime error line numbers in shadow files are +1 after the injected `use`.
* Typed/native compilation of instrumented copies is not a target; probes are
  declared with `bool` parameters, and truthy non-bool operands only work in
  the interpreter.
* Seed-runtime caveat: on the Rust bootstrap seed, file reads issued from a
  runtime-auto-invoked `main` fail with `file text input allocation failed`
  while the same reads succeed from top-level script statements. The CLI
  therefore runs as top-level script code (`mcdc_cli_main()` called at module
  level, no `main`). Tracked in
  `doc/08_tracking/bug/seed_main_entry_file_text_allocation_failed_2026-11-01.md`.

## 11. Performance

* Instrumentation: single pass, O(bytes) tokenization per logical line,
  O(tokens²) worst case for group matching on pathological lines; 158-line
  `generic_calls.spl` is instrumented in well under a second on the seed.
* Runtime: per evaluation, O(n) bit updates + one `Dict` lookup on a short
  key; file I/O only on a new distinct vector. Memory: frames are LIFO and
  shallow; rows ≤ Σ 2^n over decisions actually hit.
* Report: O(V) record decode + O(|E|² n) per decision with the 4096 cap.

## 12. Evidence

Unit specs listed in §3 assert concrete inputs (e.g. `a and (b or f(x))` →
3 conditions, postfix `c0 c1 c2 | &`, unique-cause pairs (0,1), (0,3), (2,3);
`(a and b) or c` masking pair for `c`; exact rewritten text for `if`, `while`,
`if_expr`, nested-call and multi-line cases). All 27 examples passed on the
Rust bootstrap seed (`cargo build --profile bootstrap`, 2026-11-01,
`--mode=interpreter`); no pure-Simple self-hosted binary existed on the host
that day, so these are **seed** results.

End-to-end (seed, `run --in-place`, 2026-11-01):

```
instrument: lexer_chars.spl 13 decisions / 26 conditions,
            generic_calls.spl 27 / 35, traits.spl 22 / 26, 0 skipped
run:        build/smoke_lexchars_spec.spl                  -> 21 vectors
            + trait_symbol_owner, actual_source_trait_owner_routes,
              frontend_diag_no_lowering_effect, nogc_sigil_selfhost -> 100 vectors
report:
file                                                 dec  cond   CD%  MC/DC%
src/compiler/10.frontend/core/lexer_chars.spl         13    26  74.4   69.2
src/compiler/30.types/type_infer/generic_calls.spl    27    35   0.0    0.0
src/compiler/30.types/type_infer/traits.spl           22    26   0.0    0.0
TOTAL                                                 62    87  19.5   20.7
```

The 0 % rows are the finding this tool exists to produce: none of those four
compiler unit specs drive HM generic-call inference, so the uncovered list
(27 decisions with `file:line`) is the work list for the generics-coverage
lane. Restore after the run was verified byte-identical against `git show
HEAD:`; a run killed from outside (the runner's own timeout) leaves the
instrumented copies in place, which `restore --run <name>` undoes.
