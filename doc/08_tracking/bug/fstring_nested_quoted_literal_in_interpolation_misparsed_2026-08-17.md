# f-string: a string literal on the RHS of `??` inside an interpolation is mis-parsed

(Filename says "nested quoted literal" — that was the initial, and wrong,
characterisation. The trigger is specifically the `??` right-hand side; see the
isolation table below. Filename kept stable so existing references still resolve.)
# f-string: a nested double-quoted literal inside an interpolation is mis-parsed

- **Filed:** 2026-08-17
- **Status:** **FIXED at source in BOTH parsers, and PROVEN on a purpose-built
  binary (2026-08-17).** The deployed `bin/simple` still fails — it predates the
  fix — so this stays visible until a redeploy. See "RESOLUTION" immediately below.
- **Severity:** P2 as a grammar defect. It was P1 in *effect*, because the single
  affected call site sits on `native-build`'s stderr-truncation path and its parse
  error was emitted **instead of** the real build diagnostic.

## RESOLUTION (2026-08-17) — root cause found and fixed in both parsers

The isolation in this row was right and led straight to the defect. The
"likely shape" guessed below (a special `??` path, or quote-state being dropped
after an operator) is **not** what it was; the actual cause is simpler and is an
omission, not a special case.

### Root cause

Both parsers gate whether an unescaped `"` inside an interpolation may OPEN a
nested string on a helper that asks "is this an operand position?", by testing
what the interpolation text scanned so far ENDS with. **`??` was simply missing
from that helper's operator list**, so `{q ?? "` was judged NOT an operand
position, the quote was taken to close the OUTER string, and the literal's tail
(`tmp`) fell out as a bare identifier — exactly the mechanism this row's
variant-B evidence pinned.

That helper is deliberately conservative: it was introduced for
`string_literal_brace_breaks_concat_2026-06-29` so that `"p { " + x + " }"`
keeps its `+` operators. That is why variant A (a call ARGUMENT, `paren_depth >
0`) passed while variant B (`??` RHS at `paren_depth == 0`) failed — the two
positions really are scanned by different rules, as this row suspected.

### The fix — two files, one line of logic each

**Rust seed** — `src/compiler_rust/parser/src/lexer/strings.rs`, in
`fn nested_string_may_open` (the two-char operator list):

```rust
// Null-coalescing `??` — its RHS is an operand position, so a string
// literal may legitimately open there (`{x ?? "d"}`).
for op in ["==", "!=", "<=", ">=", "??"] {
```

**Pure-Simple self-hosted frontend** —
`src/compiler/10.frontend/core/lexer_struct.spl`, in
`fn fs_nested_string_may_open` (which carries a comment naming the Rust function
as its counterpart), added alongside the existing two-char comparison test:

```simple
# Null-coalescing `??` — its RHS is an operand position, so a
# string literal may legitimately open there (`{x ?? "d"}`).
if last == "?" and prev == "?":
    return true
```

Both were changed so the two frontends do not diverge.

### Proof — binary identity and exact commands

The deployed seed cannot show this: it was built at 12:58 UTC, before the fix.
A binary was therefore built from a **clean isolated worktree containing ONLY
these two edits** (`git worktree add --detach /mnt/data/parserfix_wt HEAD`, then
the two hunks applied; `git diff --stat` in it reports exactly
`lexer_struct.spl | 4 ++++` and `strings.rs | 4 +++-`, nothing else — the shared
main working tree had unrelated uncommitted edits from parallel sessions, which
is why a worktree was used rather than building in place).

```
$ cd /mnt/data/parserfix_wt/src/compiler_rust
$ CARGO_TARGET_DIR=/mnt/data/parser_bugfix_target cargo build --release --bin simple
    Finished `release` profile [optimized] target(s) in 3m 17s
```

Binary under test: `/mnt/data/parser_bugfix_target/release/simple`,
size 59586264, mtime 2026-08-17 13:49, md5 `7ae18c5cc70671d815db2df24360b3c7`.

**Variant A+B — this row's 6-line minimal repro, unmodified:**

```
$ /mnt/data/parser_bugfix_target/release/simple run r4.spl
p=TMPDIR/x.log
```

Was ``error[E1002]: function `TMPDIR` not found``. Now matches the "applied"
(hoisted-workaround) arm's output exactly.

**Variant B — bare `??` with a string RHS, no nested call:**

```
$ cat r4b.spl
fn main() -> i64:
    val q = ""
    val tmp2 = "{q ?? "/tmp"}/x.log"
    print("p={tmp2}\n")
    0
$ /mnt/data/parser_bugfix_target/release/simple run r4b.spl
p=/x.log
```

Was ``error: semantic: variable `tmp` not found``. `/x.log` is correct: `q` is
`""`, which is not null, so `??` yields `""`. This is the variant the row warned
must be checked separately — "a fix that only repairs A+B while leaving bare B
broken would look green on the original symptom." Both are green.

Variant A was already passing and was re-confirmed unaffected earlier in the
same session on the deployed seed.

### What is NOT done

- **No redeploy.** `bin/simple` is unchanged and still exhibits the bug; the
  proof binary above is a throwaway under `/mnt/data/`. Binary-level proof for
  everyday use needs a bootstrap/redeploy.
- **The pure-Simple half is proven at SOURCE level only.** It is the exact
  mirror of the Rust hunk, in the function that names the Rust one as its
  counterpart, but the self-hosted frontend was not executed — the deployed
  binary is the Rust seed, and a pure-Simple binary would require a bootstrap
  (currently blocked, see `.claude/rules/bootstrap.md`).
- **No regression spec was added.** The row asks for one covering all three
  variants; that is still outstanding and should land with the redeploy.
- The workaround at `src/app/cli/native_build_main.spl:226` was left in place.

## Symptom

A string literal on the right-hand side of `??` inside an f-string interpolation is
mis-parsed. The scanner terminates that literal early, so its *contents* are then
read as an expression — a bare identifier, in call or variable position:
A double-quoted string literal nested inside an f-string interpolation is
mis-parsed. The interpolation scanner terminates the inner literal early, so the
literal's *contents* are then read as an expression — a bare identifier in call
position:

```
error[E1002]: function `TMPDIR` not found
  = help: check the function name or import the module that defines it
```

## The trigger is `??` with a string-literal RHS — NOT nested quotes generally

**Corrected after further isolation.** An earlier draft of this row blamed "a
nested double-quoted literal inside an interpolation". That is measurably WRONG
and would have misdirected the fix. Isolation, same binary:

| variant | source | rc | result |
|---|---|---|---|
| A | `"{pick("TMPDIR")}/x.log"` — nested literal as a call ARG, no `??` | **0** | PASSES, prints `p=TMPDIR/x.log` |
| B | `"{q ?? "/tmp"}/x.log"` — string literal as `??` RHS, no nested call | **1** | ``error: semantic: variable `tmp` not found`` |
| A+B | `"{pick("TMPDIR") ?? "/tmp"}/x.log"` | **1** | ``error[E1002]: function `TMPDIR` not found`` |

Variant A **passes**, so nested quoting inside an interpolation is fine on its
own. The necessary element is a **string literal on the right-hand side of `??`
inside an f-string interpolation**.

Variant B's error text pins the mechanism exactly: the reported missing name is
`tmp`, which is the *tail* of the literal `"/tmp"`. The scanner ends the literal
at the `"/` and then parses the remainder, `tmp`, as an identifier. When a nested
call argument is also present (A+B) the corrupted scan surfaces on the earlier
token instead, which is why the original symptom named `TMPDIR` rather than `tmp`
and sent this investigation toward the wrong hypothesis.

## Minimal repro — 6 lines, no imports

```simple
fn pick(a: text) -> text:
    a

fn main() -> i64:
    val p = "{pick("TMPDIR") ?? "/tmp"}/x.log"
    print("p={p}\n")
    0
```

Measured with `bin/simple run` on the Rust seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, size 59537240,
mtime 2026-08-17 12:58:51 UTC, md5 `78ffcbcd3f4cfaa11e3d9c1db37bf0b2`):

| arm | source form | rc | output |
|---|---|---|---|
| reverted | `"{pick("TMPDIR") ?? "/tmp"}/x.log"` | **1** | ``error[E1002]: function `TMPDIR` not found`` |
| applied | hoisted: `val root = pick("TMPDIR") ?? "/tmp"` then `"{root}/x.log"` | **0** | `p=TMPDIR/x.log` |

Both arms ran on the **same** binary — the ablation is over SOURCE, so there is
no possibility of the two arms being the same mislabeled build.

## Why this mattered out of proportion to its size

`src/app/cli/native_build_main.spl:226` used exactly this form to build the
spill-log path on the branch that runs when worker stderr exceeds
`OUTPUT_LIMIT`. Consequence: whenever `native-build` had *enough* diagnostic
output to truncate, the file on that path failed to compile, and the emitted
error was ``function `TMPDIR` not found`` rather than the actual build failure.
This is the same class of defect as the swallowed-`diagnostics` finding in
`native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17.md`:
the error-reporting path destroying the evidence for the error it was reporting.

Note the diagnostic is followed by a trailing `= help:` line, so the verdict/error
is **not** the last line of stdout — `tail -1` reads the wrong line here.

## Census

`grep -rn '"{[a-z_]*(\"' src/app src/compiler src/lib` finds exactly **two**
sites repo-wide:

- `src/app/cli/native_build_main.spl:226` — **worked around** (hoisted to a local,
  with a comment pointing here). This is the load-bearing one.
- `src/lib/nogc_sync_mut/debug_doctor/matrix.spl:335` —
  `"{_pad("target", target_w)}  {_pad("attach", attach_w)}  ..."`. **VERIFIED
  UNAFFECTED** — reproduced as a standalone fixture, rc=**0**, prints
  `target  attach  profile`. It has nested literals but no `??`, i.e. it is
  variant A above. Correctly left untouched: it was never broken.

So after the fix there are **zero** affected sites in tree, and the grammar defect
has **no** surviving in-tree reproducer. The 6-line fixture in this row is the
reproducer; a regression spec should be added when the grammar is fixed.
  `"{_pad("target", target_w)}  {_pad("attach", attach_w)}  ..."`. **NOT yet
  verified** to fail; it is left untouched deliberately so a real repro of the
  grammar defect survives in-tree. Whoever fixes the grammar should check it.

## Real fix (not done here)

The workaround normalises the call site; per the repo rule against silently
normalising a failing short form, the grammar itself is the defect and is
recorded here rather than treated as closed.

The fix belongs in the f-string interpolation scanner, and the isolation above
narrows *where*: literals as call arguments are already consumed correctly
(variant A passes), so the naive-scan-to-next-quote theory cannot be the whole
story. What fails is the literal after the `??` operator. The likely shape is that
the interpolation's expression scanner has a special path for `??` — or stops
tracking quote state once it has seen an operator at that precedence — and hands
the RHS to a scan that terminates the literal at `"/`. Anyone fixing this should
start by finding why the `??` RHS position is scanned differently from an argument
position, rather than rewriting the whole interpolation scanner.

Regression coverage to add with the fix: all three variants above, since a fix
that only repairs A+B while leaving bare B broken would look green on the original
symptom.
recorded here rather than treated as closed. The fix belongs in the f-string
interpolation scanner: when scanning an interpolation, string literals inside the
braces must be consumed as literals, with brace/quote nesting tracked, instead of
the interpolation being delimited by a naive scan to the next `"` or `}`.

## Not related to the receiver-erasure hypothesis

This defect was found while chasing
``method `compile` not found on type `object` `` in the native lane. They are
**not** the same thing, and that hypothesis is separately refuted — see
`doc/08_tracking/bug/native_build_source_closure_zero_sources_2026-08-17.md`.

## 2026-08-17 20:1x — RESOLVED on the DEPLOYED seed

Binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (bin/simple), md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45 — the REDEPLOYED seed carrying this session's fixes.

```
$ cat fstr.spl
fn pick(a: text) -> text:
    a

fn main() -> i64:
    val p = "{pick("TMPDIR") ?? "/tmp"}/x.log"
    print("p={p}\n")
    0
$ env SIMPLE_RUST_SEED_WARNING=0 bin/simple run fstr.spl
p=TMPDIR/x.log
rc=0
```

The reverted (non-hoisted) form now compiles and runs; the previous
`error[E1002]: function \`TMPDIR\` not found` is gone. Matches the
isolated-build result. **Status: RESOLVED.**
