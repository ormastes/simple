# `bin/simple test` gives wrong results for code that `bin/simple <file>.spl` computes correctly

**Status:** FIXED (2026-07-29, interpreter pass). The interpreter defect was
NOT recursion/branch-related: the tree-walking interpreter's bracket-slice
paths used a CHARACTER index space while the default engine (and the
interpreter's own index normalization) is BYTE-indexed.
`interpreter/expr/collections.rs` had two broken sites: the range-index
path (`s[a..b]`) computed indices against the character count and sliced a
char vector, and the `Expr::Slice` path (`s[a:b]`) normalized indices
against the BYTE length (`s.len()`) but then sliced a CHAR vector — an
internally mixed index space. Every byte-offset slice on multi-byte text
was silently wrong under `SIMPLE_EXECUTION_MODE=interpret`; the "minimal
isolate is correct" scoping below is explained exactly: the isolate did
only i64 arithmetic and never sliced text. Both sites now slice the byte
slice (U+FFFD substitution for a range that splits a codepoint —
byte-identical to native output when printed). Probes byte-identical across
engines after the fix (glob true, "日本語"[3:6]=="本",
"caféZdef"[-3:]=="def"); regression spec
`test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl` runs under the
forced-interpret test lane. The double-print quirk below and the
`v[-2]`-on-default-engine gap remain open, separate issues.

Historical report below (pre-fix):

**Status (superseded):** ROOT-CAUSED (2026-07-29, follow-up pass). **Severity:** every
`bin/simple test` run executes specs under the buggy engine unconditionally
— any spec whose code shape matches this bug's trigger (below) reds
regardless of whether the code under test is correct. **Not fixed** — an
interpreter-evaluation bug is out of scope for this pass; documenting
precisely per instruction, not attempting a codegen/interpreter fix.

## Root cause (PROVED, not inferred)

`bin/simple test`'s per-spec child process
(`src/app/test_runner_new/test_runner_single.spl:330-331`,
`fn main() -> i64`) unconditionally sets, before running the spec's actual
code:
```
rt_env_set("SIMPLE_RUNTIME_MODE", "interpreter")
rt_env_set("SIMPLE_EXECUTION_MODE", "interpret")
```
This forces the tree-walking **interpreter** engine for every spec run,
regardless of what `bin/simple <file>.spl` would default to on its own.

**Discriminating experiment** (same file, same path, zero test-runner
machinery involved — a plain script, run two ways):
```
$ bin/simple probe.spl                                  # default engine
RESULT=true                                              # correct

$ SIMPLE_EXECUTION_MODE=interpret bin/simple probe.spl   # forced interpreter
RESULT=false                                             # WRONG
RESULT=false                                             # (printed twice — see "Also observed" below)

$ SIMPLE_RUNTIME_MODE=interpreter bin/simple probe.spl   # the OTHER var alone
RESULT=true                                               # correct — NOT the trigger
```
`SIMPLE_EXECUTION_MODE=interpret` alone reproduces the wrong result;
`SIMPLE_RUNTIME_MODE=interpreter` alone does not. The test harness sets
both, but **`SIMPLE_EXECUTION_MODE=interpret` is the specific trigger**.

This directly reproduces the exact `bin/simple test` failure using nothing
but an env var on a plain script — conclusively locating the divergence in
the **execution engine** (default/JIT-or-native vs. forced interpreter),
not in the test harness's path resolution, caching, or spec-block
semantics.

## Investigation-guide checklist (all 4 hypotheses tested)

- **(a) test-path/module resolution divergence:** RULED OUT. Reproduced
  with a plain script at a path with zero test-runner involvement — same
  file, same `use` import, no `test/` directory, no spec framework.
- **(b) different execution engine:** CONFIRMED — this is the root cause.
  Correction to the guide's framing: it is **not** "test lane JITs where
  direct interprets" — empirically it's the reverse. Default execution
  (what `bin/simple file.spl` uses with no env override) is correct;
  forced **interpreter** mode (what the test harness always sets) is
  **wrong**. The guide's suggested "known call-boundary miscompile family"
  connection is directionally right (an engine evaluates a call-derived
  value incorrectly) but the specific broken engine is the interpreter,
  not JIT/native.
- **(c) stale `.smf` cache shadowing:** RULED OUT. Fresh worktree, `find
  <worktree> -iname '*.smf'` → 0 results before any run; no
  `.simple/`/`~/.simple` cache directory exists in this environment at
  all. Nothing to shadow.
- **(d) test-runner spec-harness semantics (it-block/return quirks):**
  RULED OUT. Reproduced with a plain `fn main(): print(...)` script — no
  `describe`/`it`/`expect`, no spec harness of any kind involved.

## Scoping: NOT simply "any call-derived local threaded into a recursive argument"

A minimal isolate with the *same shape* (extract a helper-call result to a
local, add it to an index, pass the result as a named argument to a
recursive call) evaluates **correctly under forced interpreter mode**,
even at recursion depth 5:
```
fn codepoint_len(s: text, si: i64) -> i64: ...        # same helper shape
fn recursive_probe(s: text, si: i64, depth: i64) -> i64:
    if depth <= 0: return si
    val step = codepoint_len(s, si)
    val next_si = si + step
    recursive_probe(s: s, si: next_si, depth: depth - 1)
# SIMPLE_EXECUTION_MODE=interpret: correct at depth 1 AND depth 5
```
So the bug needs more of `_glob_at`'s real shape to manifest — most likely
its **multiple early-return branches** (`*`/`?`/`[`/literal-match/`false`
all coexisting in one function with several `if ... return` guards ahead of
the recursive call) and/or genuine multi-step pattern-matching recursion
(not just repeated identical steps) — not merely "a call result in a
recursive argument position." Not narrowed further than this; a full
interpreter-internals investigation is out of scope for this pass per
instruction.

## Also reproduces in `src/lib/common/js/builtins/string.spl` (confirms it's not glob-specific)

```
$ bin/simple probe.spl                                       # default
charAt1=本                                                    # correct

$ SIMPLE_EXECUTION_MODE=interpret bin/simple probe.spl        # forced interpreter
charAt1=                                                       # WRONG (empty)
charAt1=                                                       # (printed twice, same as glob)
```
Same `string_charAt`/`text_codepoints`/`utf8_codepoint_byte_len`-walking
loop as documented in the bracket-slice fix pass. Same trigger
(`SIMPLE_EXECUTION_MODE=interpret`), same engine, confirming this is a
general interpreter-engine defect for this code shape, not something
specific to `glob.spl`'s recursion.

## Also observed, not investigated further (tangential)

Under forced interpreter mode only, both repro scripts above print their
`RESULT=`/`charAt1=` line **twice** for one `main()` call and one explicit
`main()` invocation at module scope. Not seen under default execution.
Could be an unrelated "module top-level re-executed" interpreter quirk, or
could be mechanically related to the same root cause (e.g. a retry-on-
wrong-result path). Not chased down — flagging in case it helps whoever
investigates the interpreter bug itself.

## What this is NOT

- Not a logic bug in the bracket-slice fixes (`1bd388912f5`) — proved by
  default-engine execution producing correct output for every case the
  forced-interpreter path gets wrong, same source, same session.
- Not the previously-fixed for-loop-over-text corruption
  (`doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`)
  — neither fixed function uses `for x in text:`.
- Not literally the tuple/aggregate-return corruption class
  (`doc/08_tracking/bug/native_tuple_spill_clobber_across_call_2026-07-19.md`)
  — that family is about **native/codegen** aggregate returns; this bug is
  in the **interpreter**, triggers with plain scalar (`i64`) locals (no
  tuples anywhere in the final `glob.spl`/`string.spl` source), and needs
  multi-branch recursion to manifest (see Scoping above) where that family
  needed only a single intervening call. Related in spirit (an execution
  engine mishandles a value threaded through locals across a call
  boundary) but a distinct instance — do not merge these into one bug.
- Not path resolution, not `.smf` caching, not spec-harness semantics —
  all three directly ruled out above.

## Impact

Every `bin/simple test` run forces `SIMPLE_EXECUTION_MODE=interpret` for
every spec, unconditionally (`test_runner_single.spl:330-331`, no opt-out
flag found in that file). Any spec exercising code with this bug's trigger
shape reds regardless of whether the code under test is correct — this
poisons `bin/simple test` as a verification source for that code shape
specifically, not just for the two files in this session's fix. The
`string.spl`/`glob.spl` fixes from `1bd388912f5` remain landed; re-verify
them via default-engine execution (see Reproduce) until the interpreter bug
itself is fixed, not via `bin/simple test`.

## Reproduce

```
cd <fresh worktree, built bin/simple symlink>

cat > probe.spl <<'EOF'
use std.nogc_sync_mut.glob.{glob_match}
fn main():
    print("RESULT={glob_match(\"café.txt\", \"caf?.txt\")}")
main()
EOF

bin/simple probe.spl                                # RESULT=true (correct)
SIMPLE_EXECUTION_MODE=interpret bin/simple probe.spl # RESULT=false (WRONG)
SIMPLE_RUNTIME_MODE=interpreter bin/simple probe.spl # RESULT=true (correct -- isolates the trigger var)
```
