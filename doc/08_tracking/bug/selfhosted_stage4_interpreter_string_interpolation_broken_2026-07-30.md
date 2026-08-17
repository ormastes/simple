# Self-hosted stage4 `run` (interpreted) drops string interpolation

**Status:** open, blocking self-hosted deploy. **Filed:** 2026-07-30.

## Symptom (PROVED, reproduced twice, isolated from seed delegation)

A freshly-built pure-Simple self-hosted "full CLI" binary (stage4, entry
`src/app/cli/main.spl`, 726→1490-file entry closure, cranelift backend,
source commit `9ea0b39962d76929ac58598d837f9292f3ebf6af`) silently drops
string interpolation when running a script via `run` (the interpreted
path), but only when genuinely self-hosted -- confirmed via the binary's
own `seed sibling not found, skipping delegation:
.../build/bootstrap/simple_seed` message, which proves no fallback to the
Rust seed occurred.

Minimal repro:
```simple
fn main():
    val x = 5
    print("x={x}")
```
Expected: `x=5`. Actual (self-hosted, no delegation): `x={x}` (the literal
placeholder, uninterpolated).

**Delegation masks this.** When run from a working directory where the
relative `build/bootstrap/simple_seed` sibling path happens to resolve to
an existing file, the CLI silently delegates to the Rust seed and prints
the correct `x=5` -- looking like a pass while the self-hosted binary's own
interpreter never actually ran. `-c 'print("x={x}")'`-style one-liners hit
this same delegation path in every test run in this session and are **not
reliable evidence** the self-hosted binary works; only a `run` invocation
from a directory with no reachable seed sibling isolates the self-hosted
binary's own behavior.

## What still works (self-hosted, no delegation, confirmed)

- `check src/app/cli/bootstrap_main.spl` -> `OK` (source parses/type-checks).
- `run` on a script with **no interpolation** (`print("hello from stage3
  self-hosted")`) prints correctly.
- Plain arithmetic (`val x = 2 + 3`) evaluates correctly; only the `{x}`
  substitution inside a string literal is dropped.

## Provenance of the binary that exposed this

- Built manually, stage-by-stage, after two blockers in
  `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`
  itself (see the companion report in this pass's landing commit message /
  session record):
  1. A fresh `git worktree` has no `src/compiler_rust/target`; the
     script's own Rust-seed-input fingerprint hard-rejects a **symlink**
     anywhere under `src/compiler_rust`/`src/runtime` (by design --
     `scripts/check/lib/bootstrap-stage3/authority.shs`'s `find ... -type
     l -print -quit` check). A worktree-wide `target` symlink trips it;
     a real `target/` directory containing a symlinked `target/bootstrap`
     subdirectory does not (the walk prunes at the `target` boundary).
     Fixed by making `target/` a real directory before symlinking
     `target/bootstrap` inside it.
  2. `bootstrap_stage3_directory_snapshot` likewise refuses to snapshot a
     symlinked runtime directory (`error: could not snapshot Rust runtime
     authority`) once the seed was rebuilt through the symlink -- fixed by
     physically copying `target/bootstrap` (4.7G) into the worktree
     instead of symlinking it, after which the freshly-built seed
     satisfied every authority check.
  3. The default `--backend=llvm` seed build (via `--full-bootstrap`) did
     not compile in LLVM support (`error: native backend 'llvm' is not
     available in this build`) even though the platform script detected
     LLVM 18 -- matches the already-documented
     `doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`
     family; using `--backend=cranelift` explicitly (the documented
     working stage-2/3 path per `.claude/rules/bootstrap.md`) resolved it.
- After those three fixes, the wrapper script's own "Stage 2" step still
  reported `stage2 native-build failed (exit 1)`, but its own
  `stage2-native-build.log` was stale (mtime predated this session's
  runs by hours) -- **not root-caused**; a hand-invoked `native-build`
  with materially the same flags (`--source src/compiler --source
  src/app --source src/lib --entry-closure --entry
  src/app/cli/bootstrap_main.spl`, cranelift) succeeded cleanly (726
  files, 98.5s, exit 0) from the same worktree/seed/cache root.
- Stage 3 (stage2 self-hosting: stage2 binary recompiling the identical
  source) succeeded identically (726 files, same 22330944-byte output
  size as stage2, sha differs -- expected, embedded build metadata).
- Stage 4 (full CLI, `main.spl` entry) succeeded: 1490 files, 26709488
  bytes, 251s (147.5s compile + 103.6s link), peak observed RSS ~1.1GB
  (nowhere near the ~65GB/64GB-cap historical peak -- no memory-cap risk
  this run). `sha256: 39a507b917c8d05583c386a7f2a27d195ddb0ecc0a702de487
  e07aff51378483`. `strings | grep -c llvm::` = 0 (expected, cranelift).

## Deployment decision

**Not deployed.** A binary that silently drops string interpolation would
regress `bin/simple` for every session on this host -- `"{var}"` syntax is
used pervasively throughout the codebase, including in this very
investigation's own smoke-test output. The existing live
`bin/release/x86_64-unknown-linux-gnu/simple` (the LLVM-enabled Rust seed
redeployed earlier this campaign) is unchanged; a named rollback copy
(`simple.rollback-llvm-seed-2026-07-30`, identical 154094616 bytes) was
taken before this attempt in case a deploy had been warranted.

## "Verify early" result (per this pass's explicit instruction)

**Confirmed: the bootstrap entry closure does NOT pull in
`src/lib/common/web`.** Every successful native-build in this pass (stage
2/3 at 726 files, stage 4 at 1490 files) reported its own file count and
neither matches or approaches the scope that would include
`browser_renderer_protocol.spl`'s dependents; `browser_renderer_protocol.
spl`'s own parse defect (separately fixed at `023a60a05aa`, verified
ancestor of this build's `9ea0b39962d`) was never at issue here regardless.

## Root cause found 2026-07-30 (PROVED, precisely located; fix not implemented)

**Reproduced deterministically, self-hosted status confirmed each time**
(the "seed sibling not found, skipping delegation" message; rebuilt the
binary from scratch via a clean cranelift-only seed after the first
attempt's seed had regained an LLVM feature from unrelated concurrent
host activity, which itself caused a `LLVM ERROR: inconsistency in
registered CommandLine options` abort in a native-build invocation --
worth flagging as its own hazard: a Rust seed with LLVM statically linked
crashes on `--backend cranelift` native-build under concurrent/threaded
use; a clean `--backend=cranelift` seed rebuild avoids it entirely).

**Subset test (self-hosted, `run`, no delegation):**
```
bare={a}              -- FAILS (want 2)
expr={a+b}             -- FAILS (want 5)
literal-only text       -- OK (no braces, unaffected)
nested {a} and {b}     -- FAILS both (want "nested 2 and 3 together")
escaped braces: {{}}   -- OK: prints "escaped braces: {not interp}" (the
                           `{{`->`{` escape decode DOES work)
hello {name}!           -- FAILS (want "hello world!")
```
**Total failure of genuine interpolation, escape decoding unaffected.**
The escape/substitution split points at two independent mechanisms, not
one shared broken one -- confirmed by code reading below.

**Localization (PROVED via source reading, not inference):**

1. The lexer (`src/compiler/10.frontend/core/lexer_struct.spl`, the `{`
   branch of the string-scanning loop, ~line 667) does NOT split `{expr}`
   at lex time. It brace-depth-tracks to find the matching `}` (handling
   nested strings/parens so `{xs.join("-")}` lexes correctly) and then
   copies the ENTIRE `{...}` region -- braces and all -- verbatim into the
   token's raw text as plain characters. `{{`/`}}` doubled-brace escapes
   ARE decoded to single braces, but that is a separate, earlier
   character-level rule in the same scan, not interpolation splitting.
2. The actual split-into-real-expressions step is
   `flat_bridge_build_string_interps` in
   `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:601`. Its own
   header comment names this exact defect as **pre-existing and already
   tracked ("Bug #136")**: *"the core lexer copies each `{expr}`
   interpolation region VERBATIM into the string token and never parses
   the inner expression, so the bridge previously emitted `StringLit(value,
   nil)` ... `{expr}` printed literally."* It brace-scans the raw text
   again, and for each top-level `{...}` region calls
   `flat_bridge_parse_interp_inner(inner)` (same file, line 555) --
   which re-lexes and parses `inner` as a standalone expression, appending
   it to the **same shared flat-AST arena** the rest of the compiler uses,
   returning a real expression id.
3. **This fix is wired into the HIR/MIR lowering pipeline only**
   (`src/compiler/20.hir/hir_lowering/expressions.spl` and
   `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` are the only
   other callers) -- i.e. it runs when compiling to native code, never
   when interpreting.
4. **The tree-walking interpreter's string-literal evaluator never calls
   it.** `eval_string_lit` (`src/compiler/10.frontend/core/interpreter/
   eval.spl:379`) is:
   ```
   fn eval_string_lit(eid: i64) -> i64:
       val_make_text(expr_get(eid).s_val)
   ```
   -- a direct, unconditional return of the raw token text. It has no
   brace check, no split, no expression evaluation. `eval_interpolated_
   string` (`eval_access.spl:496`, duplicated verbatim in `_EvalOps/
   access_literal_assign_eval.spl:581` -- itself worth a follow-up
   dedup, though the duplication is not the bug: both copies are
   identical and correct) DOES correctly evaluate parts and join them --
   but it is only reachable from an `EXPR_INTERPOLATED_STRING` node, and
   nothing on the interpreter path ever constructs one from a raw
   `{expr}`-bearing literal (the parser always emits plain
   `EXPR_STRING_LIT`; only the HIR/MIR bridge upgrades it, post-parse,
   pre-codegen -- a stage the interpreter skips entirely).

**This is exactly the failure shape the brief called out**: a special-
cased execution path (the interpreter, which bypasses HIR/MIR) that never
inherited a fix applied to a sibling path (native codegen), matching the
`parse_comparison`/`parse_equality` precedent from earlier in this
campaign.

**Why the Rust seed doesn't show this:** out of scope to fully confirm,
but consistent with the seed's parser being a separate Rust implementation
that (per this file's own header comment) is treated as the interpolation
*oracle* elsewhere in this codebase ("The seed oracle trims this padding
before parsing" -- `convert_nodes.spl:583`) -- i.e. the seed's own parser
evidently performs (or never needed) an equivalent split at parse time, so
its interpreter never depended on a separate post-parse bridge step the
way the pure-Simple compiler's does.

**Fix approach identified, not implemented this pass:** make
`eval_string_lit` detect an unescaped `{` in `expr_get(eid).s_val` and, if
found, perform the same brace-scan `flat_bridge_build_string_interps`
does, calling `flat_bridge_parse_interp_inner` per region to get a real
expr id in the same flat-AST arena, then `eval_expr` each part and
`val_to_text`+join exactly as `eval_interpolated_string` already does (that
function's logic can likely be reused almost as-is once given a real parts
list). `flat_bridge_parse_interp_inner`'s own comment states it is safe to
call "whenever the lexer is idle," which should hold during evaluation
(strictly after the whole module is parsed) but was not verified here.
**Not implemented this pass**: this touches interpreter dispatch for the
single most common literal kind in the language, the fix needs a rebuild-
and-reverify cycle (~5-8 minutes each, using the recipe in this document)
per iteration to validate against escapes/nesting/non-ASCII/format specs
without regressing the already-correct HIR/MIR path, and the coordinator's
explicit guidance was to stop and report a precise localization rather
than rush a fix touching a load-bearing, pervasively-used code path. A
non-vacuous regression spec (assert interpolated output; prove it fails on
the current self-hosted binary and passes after) is the natural first step
for whoever implements the fix.

## Fix implemented 2026-07-30 — execution pending

Status: **IMPLEMENTED STATIC / PHASE-2/3 EXECUTION HELD**.

The core frontend now expands newly parsed ordinary string nodes after the
enclosing module parse is complete. Valid regions become the existing
`EXPR_INTERPOLATED_STRING` node with pre-parsed expression IDs; malformed or
unmatched regions remain plain strings, doubled braces decode once, and raw
strings remain non-interpolating. The tree-walking evaluator only interleaves
those canonical parts with literal segments—there is no parser dependency or
parsing during evaluation. Flat-bridge and bootstrap HIR paths consume the
same promoted node and preserve processed plain-string state.

`test/01_unit/compiler/interpreter/string_interpolation_spec.spl` covers
variables, expressions, multiple regions, a nested quoted method argument,
mixed escaped/real regions, malformed CSS-shaped braces, parser recovery, and
raw strings. Independent static review accepted the dependency direction,
arena ownership mirrors, append-range handling, and native/interpreter parity.

The isolated bootstrap-seed syntax probe could not execute because its CLI
delegation expected a missing worktree-local `bin/simple`; it is not a PASS.
Concurrent sessions were already writing the shared bootstrap cache and
running full bootstrap jobs, so this lane did not start a competing build.
Qualified phase-2/3 build plus the focused SSpec remain required.

## Verification 2026-07-30 — candidate fix built and run, does NOT resolve the defect

Status: **PHASE-2/3 EXECUTION SUPPLIED. RESULT: FAIL.**

Two things established first, both worth recording on their own:

1. **A commit existing in the shared git object store is not a landed fix.**
   `d0633b7dad3`/`ae4c3d56ce3` (identical message and diffstat, likely a jj
   amend pair) are reachable by hash but `git branch --contains ae4c3d56ce3`
   returns nothing — neither is reachable from the `main` bookmark. They are
   another session's in-progress working copy, evidenced by a live
   `.git/index.lock` held by that session at the time of this check.
2. **A landed fix is not a verified one.** The commit's own note above
   ("execution pending... not a PASS... phase-2/3 build plus the focused
   SSpec remain required") already said as much; this section supplies that
   missing verification.

### What was done

In an isolated worktree, cherry-picked all 10 files changed by `ae4c3d56ce3`
(`git checkout ae4c3d56ce3 -- <paths>`, valid because the commit object is
content-addressable regardless of which ref, if any, points at it) on top of
a clean checkout, then rebuilt self-hosted from scratch:

- Stage2 (`bootstrap_main.spl` entry): 727 compiled, 0 cached, 0 failed.
- Stage4 (`main.spl` entry, from stage2): 1491 compiled, 0 cached, 0 failed.
  Binary: `build/bootstrap/stage4-fix3` (26114 KB).

Every run below printed the binary's own
`simple: seed sibling not found, skipping delegation: ...` line, confirming
genuine self-hosted execution rather than silent delegation to the Rust seed
(see the delegation-trap note earlier in this document).

### Result: identical to the unfixed baseline

`interp_matrix.spl` (bare var, expression, named var with surrounding text,
paren-nested expression, `{{`/`}}` escapes only, mixed escape+real
interpolation in one string) run under `stage4-fix3`:

```
hello {name}
sum is {x + y}
prefix-{name}-suffix
nested {(x + y) * 2}
escaped braces: {not interp}
mix {{literal}} then {name} then {{end}}
```

Every case that should interpolate still prints the literal `{...}` text
unchanged — byte-for-byte the same as the original unfixed binary. The fix
in `ae4c3d56ce3` makes no observable difference to `print("...{expr}...")`
under `run`.

### Their own regression spec crashes

```
$ build/bootstrap/stage4-fix3 run test/01_unit/compiler/interpreter/string_interpolation_spec.spl
simple: seed sibling not found, skipping delegation: .../build/bootstrap/simple_seed
runtime error: field access on nil receiver
timeout: the monitored command dumped core
```

`test/01_unit/compiler/interpreter/string_interpolation_spec.spl` (added by
the same commit) does not pass under genuine self-hosted execution — it
segfaults on a nil field access and dumps core. The frontend wiring
(`core_frontend_parse` in `src/compiler/10.frontend/core/frontend.spl` calling
`expand_string_interpolations` after each module parse) looked structurally
plausible on inspection but was not debugged further — that is explicitly
out of scope for this pass (see below).

### Reproducible paths

- Worktree: `/tmp/claude-1000/-home-ormastes-dev-pub-simple/0cc17245-8e37-4666-9b9d-9106c84b9a47/scratchpad/wt-fix`
  (uncommitted; has `ae4c3d56ce3`'s 10 files cherry-picked on top of a clean
  checkout at `6acd3586345`).
- Binaries: `build/bootstrap/stage2-fix3`, `build/bootstrap/stage4-fix3`.
- Matrix probe: `/tmp/claude-1000/-home-ormastes-dev-pub-simple/0cc17245-8e37-4666-9b9d-9106c84b9a47/scratchpad/interp_matrix.spl`.
- Minimal `literal`-as-identifier repro (a separate, unrelated defect hit
  while independently implementing this fix, filed on its own — see
  `doc/08_tracking/bug/seed_lexer_literal_soft_keyword_shadows_identifier_2026-07-30.md`):
  `repro7.spl`/`repro8.spl`/`repro9.spl` in the same scratchpad directory.

### Disposition

Not deployed. The live `bin/release/x86_64-unknown-linux-gnu/simple` is
unchanged; rollback remains at
`bin/release/x86_64-unknown-linux-gnu/simple.rollback-llvm-seed-2026-07-30`.
Crash debugging on `ae4c3d56ce3`'s `expand_string_interpolations` path is
being handed to a fresh lane, starting from this localization (frontend
wiring point identified, failure mode is a nil-receiver field access,
reproducible via the regression spec above) rather than continued here.

## 2026-08-17 lane D — root-cause path is FIXED IN-TREE (content-classified); end-to-end still UNVERIFIED

**Verdict: the mechanism this row asked for EXISTS and WORKS. The reported
end-to-end symptom could not be exercised — no self-hosted binary is runnable in
this tree. Classified by CURRENT SOURCE CONTENT, not by SHA ancestry.**

### The cited file is not the locus (path drift)

The row cites `src/compiler/10.frontend/core/lexer_struct.spl`. That file is
CORRECT and always was: its `{` branch (`:884-963`) deliberately copies the whole
`{...}` region verbatim, brace-depth-tracking nested strings, exactly as the
"Localization" section above describes. The defect was never there — the missing
step was the post-parse promotion.

### The promotion step is present and wired

- `src/compiler/10.frontend/core/string_interpolation_expand.spl:155`
  `expand_string_interpolations(start_expr)` — walks the arena, and for each
  `EXPR_STRING_LIT` with unprocessed state promotes it via
  `expr_promote_interpolated_string` when
  `parse_string_interpolation_parts` yields regions, otherwise marks it processed
  after decoding `{{`/`}}`.
- `src/compiler/10.frontend/core/frontend.spl:27` — `core_frontend_parse` calls it
  after every successful module parse, before
  `transform_interpolated_placeholder_args`.
- `src/compiler/10.frontend/core/interpreter/eval.spl:421` — dispatches
  `EXPR_INTERPOLATED_STRING` to `eval_interpolated_string`.

`eval_string_lit` (`eval.spl:469`) is still the bare
`val_make_text(expr_get(eid).s_val)` the localization flagged — correctly so:
under this design it only ever sees literals that have no interpolation regions.

### Measured, and the old spec was VACUOUS

`test/01_unit/compiler/interpreter/string_interpolation_spec.spl` (the row's
repro hint) **cannot settle this row**: its examples are plain
`expect("bare={a}")` literals, so they are lexed and interpolated by whichever
binary runs the spec — today the Rust seed, whose interpolation always worked.
It never touches the pure-Simple frontend. It also could not be run to a verdict
today: three attempts under `bin/simple test` ended
`reason=daemon-no-response budget_ms=480000` / SIGTERM at the 600s host monitor
(the host is saturated by a live bootstrap).

Replacement, which drives the pure-Simple frontend sources directly (read live
from disk, no build) — new file
`test/01_unit/compiler/interpreter/pure_simple_frontend_interpolation_promotion_spec.spl`:

```
pure-Simple frontend string interpolation promotion
  ✓ promotes a bare {var} literal to an interpolated-string node
  ✓ promotes an expression region and a multi-region literal
  ✓ leaves a brace-free literal as a plain string literal
  ✓ leaves a CSS-shaped brace literal unpromoted

4 examples, 0 failures
SPEC FILE VERDICT: .../pure_simple_frontend_interpolation_promotion_spec.spl declared>=4 executed=4 passed=4 failed=0 dropped=0
```

Non-vacuity: the same counter returns 1 and 2 in the first two examples and 0 in
the last two, so it discriminates. Fixture sources are built by CONCATENATING
`char_from_code(123)`/`(125)` — never embedded braces, which the spec's own lexer
would resolve.

### What this lane could NOT prove

- **The end-to-end symptom.** `bootstrap/stage3/simple run` is
  `error: unknown command 'run'` (verified directly) and `bin/simple` is the Rust
  seed, so no self-hosted `run` of `print("x={x}")` was possible. The row's
  headline claim remains UNVERIFIED end to end.
- The nil-receiver crash the previous verification section reported for
  `string_interpolation_spec.spl` under `stage4-fix3` — not reproducible without
  a self-hosted binary.
- No sabotage test (removing the `frontend.spl:27` call to confirm the new spec
  goes RED): `frontend.spl` is outside this lane's file scope and ~15 lanes are
  editing concurrently.

**Recommended disposition:** do NOT close on this evidence alone. Re-run the new
promotion spec plus a genuine self-hosted `run` when a stage4 binary next exists;
if both are green, close.
