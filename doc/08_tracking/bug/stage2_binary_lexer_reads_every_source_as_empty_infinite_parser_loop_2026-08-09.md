# Stage-2 binary lexes EVERY source file as empty → unbounded parser-error loop

Date: 2026-08-09
Status: **FIXED AND VERIFIED END-TO-END (2026-08-09, run 6).** The
`CoreLexer.handle_indentation()` fix (`d37b5e578b4`) is confirmed by a real
bootstrap: a Stage-2 binary built from it lexed *and parsed* the full
`bootstrap_main.spl` (21,918 bytes) and ran on into module assembly, with
`lexer_fatal` count **0** across the entire run. Stage 3 now fails **further
downstream**, in `FlatAstBridge.flat_ast_to_module` (SIGSEGV/139) — a different,
newly-revealed blocker tracked in
`stage3_selfhost_segv_in_flat_ast_to_module_2026-08-09.md`. See "2026-08-09
run 6" at the BOTTOM for the evidence and the one caveat (the verifying run
needed `36673b6b6a3` reverted, because pristine `origin/main` cannot link
Stage 2 — see `stage2_native_build_link_undefined_method_symbols_2026-08-09.md`).

Earlier status (run 5): root cause found and fixed, end-to-end verification
outstanding. The run-4 native-codegen hypothesis below is **disproven**, and the
real defect is a no-token return path in `CoreLexer.handle_indentation()` that
reproduces in the interpreter with no bootstrap at all. The rest of this
document is preserved as the investigation record; read it knowing run 4's
conclusion was wrong.

Earlier status (run 4): **REOPENED — NOT FIXED.** The 2026-08-09 fix (bfd9284618a) was verified
only through the interpreter path. A full bootstrap at that exact commit
(2026-08-09, 12:34-12:58) rebuilt Stage 2 and the dead lexer **recurred
immediately**: Stage 3 died on its own entry file with
`[lexer_fatal] ... next_token() produced kind 0`. The fix's central premise —
that `next_token()`'s **by-value return** is reliable where the field read-back
was not — is **empirically false**: the returned value is 0 too. See
"2026-08-09 run 4" below. Two of the three landed changes DID work and should be
kept (the fail-closed guard and the forward-progress invariant turned a
444 MB/32 GB runaway into a 195-byte diagnostic). A third defect was found: the
strengthened admission gate is **still fail-open**, for a newly-identified
reason (`--entry`).
Area: bootstrap / stage-2 native-build / 10.frontend lexer / parser error recovery

## Summary

A full `--full-bootstrap` from a clean pinned `origin/main`
(`f026cfcf510d12758048c1bad585ccd59d9764fa`) produced a Stage-2 binary that
reports **806 compiled, 0 failed**, links a 126 MB executable, and **passes the
"Stage 2: running bootstrap compiler sanity" gate** — yet that binary **cannot
lex a single source file**. Every file, including a hand-written two-line one,
is read as an empty token stream, and the parser's error recovery then loops
**forever** without advancing.

This is a **silently vacuous Stage 2**: the build is green on every signal the
wrapper checks, and the artifact is non-functional.

## Reproduction (exact)

```
SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=/home/ormastes/dev/simple-build-out/stage3-nilrecv-20260809-v3 --progress
```

Checkout: `/home/ormastes/dev/simple-s3verify-20260809`, pinned to
`f026cfcf510`, `git status` clean apart from pre-existing CRLF noise in 10
`.cmd`/`.bat` files. Host at launch: load 8.2, 1.4 T free on `/`, 108 G RAM
available.

## Evidence

### 1. Stage 2 reports complete success

`logs/x86_64-unknown-linux-gnu/stage2-native-build.log` in full (358 bytes):

```
Linked: .../stage2/x86_64-unknown-linux-gnu/simple (126193 KB) via clang++
Build complete: 806 compiled, 0 cached, 0 failed
  Binary: .../stage2/x86_64-unknown-linux-gnu/simple (126193 KB)
  Time: 125.9s compile + 68.5s link = 194.3s total
```

The wrapper then printed `Stage 2: running bootstrap compiler sanity` and
admitted the binary to Stage 3.

### 2. The binary runs, but its lexer is dead

The binary itself is alive and is not size-vacuous (129,222,000 bytes):

```
$ .../stage2/x86_64-unknown-linux-gnu/simple --version
simple-bootstrap 1.0.0-beta          # rc=0
```

But `native-build` on a **two-line file written by hand** fails identically to
the real entry point:

```
$ printf 'fn main():\n    print("hi")\n' > probe_tiny.spl
$ .../stage2-admitted/simple native-build --target x86_64-unknown-linux-gnu \
    --backend llvm -o /tmp/s3probe/tiny probe_tiny.spl
[parser_error] line 1:1: unexpected token in expression: Unknown(0) ''
[parser_error_ctx] path probe_tiny.spl kind 0 text ''
[parser_error] line 1:1: unexpected token in expression: Unknown(0) ''
[parser_error_ctx] path probe_tiny.spl kind 0 text ''
... forever
```

`text ''` and `Unknown(0)` at `line 1:1` mean the lexer handed the parser an
**empty/unknown token for a non-empty file**. This is not entry-file specific
and not source specific — it is every file.

### 3. The parser error-recovery loop is unbounded

Stage 3 ran 11 minutes and produced:

- `stage3-native-build.log` = **444,103,752 bytes / 6,299,344 lines**
- `sort -u` over the **entire** log = **2 distinct lines** (the pair above)
- process at **100% CPU** (TIME 11:09 / ELAPSED 11:13) and **32.4 GB RSS**, still climbing

So the failure is not merely a bad diagnosis — error recovery makes **no
forward progress**, and both the log and RSS grow without bound. Left alone
this fills the disk or OOMs the host. (This is the same hazard class that wiped
`main` twice via ENOSPC on 2026-08-01; the run was killed deliberately.)

### 4. It is NOT a checkout artifact — ruled out explicitly

- entry file on disk: `src/app/cli/bootstrap_main.spl`, **21,918 bytes**, real
  content (`extern fn sys_get_args() -> [text]` …), `git diff HEAD` on it is
  **empty** — byte-identical to the pinned blob.
- the failing process's `cwd` is `/home/ormastes/dev/simple-s3verify-20260809`
  (read from `/proc/639991/cwd`), and the entry file **is** visible and readable
  at exactly the relative path passed on the command line.
- the **Rust seed** read those same 806 files fine while building Stage 2. Only
  the produced pure-Simple binary cannot read them.

## Where to look

The lexer/tokenizer used by the pure-Simple `native-build` path returns an empty
token stream for a file whose bytes are present. Two independent defects are
stacked here and BOTH deserve fixing:

1. **The lexer returns empty for a non-empty file** (the root cause).
2. **The parser's error recovery does not guarantee forward progress** — on an
   unconsumable token it re-reports at the same position forever instead of
   advancing or aborting. Even after (1) is fixed, (2) will turn any future
   lexer defect into an unbounded disk/OOM event rather than a diagnosis. A
   bounded error count / mandatory-advance invariant belongs in the parser loop.

## Gate defect (file/fix separately if not already tracked)

**`Stage 2: running bootstrap compiler sanity` is fail-open.** It admitted a
compiler that cannot parse a two-line file. A sanity gate that a
totally-non-functional binary passes provides no signal. Minimum bar: compile a
trivial fixture end-to-end and assert a non-vacuous artifact plus a bounded
runtime — the exact probe used in Evidence §2 would have caught this in seconds.

## Consequence for the nil-receiver SIGILL bug

This is **blocker 12** in front of
`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`. Stage 3
never reached HIR or MIR lowering — it never got past lexing its entry file — so
the SIGILL fault site **still has never executed**. Measured over the full
444 MB Stage-3 log: `field access on nil receiver` = 0, `SIGILL`/exit 132 = 0,
`[mir-stmt-caller]` = 0, `garbage-expr` = 0. Both probes were enabled and both
produced nothing.

---

## Root cause (2026-08-09, found)

`core/lexer.spl:lex_next()` threw away the token kind **returned** by
`CoreLexer.next_token()` and instead read `loaded.cur_kind` back off the struct:

```
    var _scan_kind: i64 = 0
    ...
    _scan_kind = loaded.next_token()      # correct value, discarded
    val kind = loaded.cur_kind            # <-- read-back, returned 0
```

`CoreLexer` is a **value-type `struct`** (`lexer_struct.spl:135`) held in a
module-level array slot (`current_core_lexer_slot`). In the Stage-2 native
binary the `me`-method mutation of `self.cur_kind` was not visible to this
caller, so the read-back yielded the **constructor default `cur_kind: 0`**
(`make_core_lexer`, `lexer_struct.spl:167`) for every token.

Three observations from the bug report all fall out of this exactly:

- `Unknown(0)` — 0 is not a token kind at all; it is only the struct's
  zero-initialiser. `scan_token()` always routes through `make_token()`, which
  is never called with 0.
- `text ''` at `line 1:1` — those came from the module-level `core_last_token_*`
  slots that `make_token()` **does** write. `1:1` is `self.line`/`self.col` on
  an unadvanced lexer, and `''` is `make_token(190, "", …)`. So the scan really
  did run and really did reach EOF; only the kind read-back was lost. The token
  stream was therefore **not** "empty because the file was unread" — the file
  read is fine.
- the infinite loop — `parse_module_body()`'s `while true` has exactly ONE exit,
  `par_kind_get() == 190`. A kind permanently stuck at 0 makes that exit
  unreachable, and the module-level fallback arm re-runs `parse_expr()` at the
  same position forever.

Corrected diagnosis of the report's §"Where to look": there is **one** root
defect, not "a dead lexer plus a recovery bug". The lexer's file reading and
tokenizer are both correct.

## Fixes

1. **`src/compiler/10.frontend/core/lexer.spl`** — `lex_next()` now uses
   `_scan_kind`, the value `next_token()` returns by value (computed while
   `self` is live), eliminating the struct read-back. It additionally fails
   **closed** on the impossible kind 0: one bounded `[lexer_fatal]` diagnostic
   naming path/line/col/source-length, then the stream terminates at EOF (190)
   instead of handing the parser an unconsumable token forever.
   `lex_init_with_path()` also reports once when a **named** source file reaches
   the lexer as empty text.
2. **`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`** —
   forward-progress invariant on `parse_module_body()`'s loop. The
   `(kind, line, col)` triple at the top of each iteration must differ from the
   previous iteration's; if it repeats, one error is emitted and the loop
   breaks. Any future lexer/parser defect of this shape now yields a bounded
   diagnosis instead of a 444 MB disk/OOM event.
3. **Gate fail-open (see below).**

## Gate defect — root cause and fix

The gate was **not** weak in the way the original write-up assumed: it already
native-builds `p2_add.spl` end-to-end and asserts `stdout == 5`
(`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:
candidate_frontend_smoke`). The real hole is a **configuration mismatch**:

- the gate runs the candidate with **`SIMPLE_BOOTSTRAP=0`**
  (`candidate_frontend_admission.shs`),
- Stage 3 runs the same admitted binary with **`SIMPLE_BOOTSTRAP=1`**
  (`bootstrap-from-scratch.sh`, Stage-3 `env` block).

`SIMPLE_BOOTSTRAP=1` is documented in this repo to change compiler behaviour
drastically (vacuous `--native` emit; the `?` operator dropped). The gate was
certifying a configuration Stage 3 never uses.

Fixes in `candidate_frontend_admission.shs` + `bootstrap-from-scratch.sh`:

- `candidate_frontend_smoke` takes `CANDIDATE_FRONTEND_BOOTSTRAP`, and
  `bootstrap_stage_sanity` now runs it **twice — once per `SIMPLE_BOOTSTRAP`
  value** — recording `frontend_smoke_bootstrap_mode_status` in the evidence
  file.
- Runaway-output cap (`CANDIDATE_FRONTEND_MAX_LOG_BYTES`, default 4 MiB): a
  candidate that emits more than that for a two-line fixture is rejected **even
  when its build exits 0 and its binary prints 5** — precisely the 2026-08-09
  shape, where every signal the gate checked was green.
- Dead-lexer signature rejection: `Unknown(0) ''` or `[lexer_fatal]` anywhere in
  the candidate's build output is fatal.
- The failure path now `head -c 65536`s the candidate log instead of `cat`ing
  it, so a runaway candidate cannot flood the bootstrap log through the gate.

## Regression evidence

- `test/01_unit/compiler/frontend/lexer_dead_stream_forward_progress_spec.spl`
  — **5 examples, 0 failures** (`Results: 5 total, 5 passed, 0 failed`).
  Covers: the exact two-line probe from §Evidence 2 parsing to one `DECL_FN`
  named `main`; a three-declaration module reaching EOF; bounded termination on
  a single and on repeated unconsumable module-level tokens; and an empty
  module parsing to zero decls.
- `scripts/check/check-frontend-smoke-rejects-dead-lexer.shs` — **PASS — 5 gate
  case(s) checked (1 admit, 4 reject)**. Uses fake candidate binaries, so it
  needs no bootstrap. The admit case is the non-vacuity control; the reject
  cases include two that exit 0 and produce a *working* binary and are rejected
  purely on the runaway-output and dead-lexer signatures.
- No regressions: `lexer_position_unification_spec.spl` 4/4,
  `lexer_comprehensive_spec.spl` 2/2.

## 2026-08-09 run 4 — full bootstrap AT the fix commit: the bug RECURS

The outstanding step listed below ("no full bootstrap was run after the fix")
was executed. Result: **the fix does not work.**

Setup: `origin/main` == `bfd9284618a6647e1ff34a107e8b819c76561f94` (the fix
commit itself — verified as an ancestor, and in fact the tip). Fresh 112,239-file
checkout via `git archive | tar -x` + alternates at
`/home/ormastes/dev/pub/simple_bootstrap_wt_20260809`. Host at launch: 1.3 T free,
load 13.95, 94 G RAM available. Command exactly as specified in §Reproduction,
output to `/home/ormastes/dev/pub/bootstrap_out_20260809`.

### What succeeded

- Rust seed, native-all, runtime-nolto, compiler-backfill: all built clean.
- **Stage 2 built clean: `Build complete: 808 compiled, 0 cached, 0 failed`**,
  linked 126,202 KB in 205.0 s. (Compare the broken run: 806/0/126,193 KB. The
  numbers are nearly identical — a green Stage 2 has now been shown **twice** to
  carry no information about whether the frontend works.)
- The sanity gate **passed** and admitted the binary to Stage 3.

### What failed — the dead lexer, verbatim

`logs/x86_64-unknown-linux-gnu/stage3-native-build.log`, in full (195 bytes):

```
[lexer_fatal] dead lexer: next_token() produced kind 0 (never a valid token kind)
for path 'src/app/cli/bootstrap_main.spl' at line 1 col 1; source length 21918.
Terminating token stream at EOF.
```

This is the fix's **own** fail-closed diagnostic firing. It proves the negative
directly: `_scan_kind = loaded.next_token()` returned **0**. The correction the
commit made — stop reading `loaded.cur_kind` back, use the return value — does
not help, because the return value is equally dead.

Independent reproduction of §Evidence 2 against the freshly-built binary
(sha256 `60cf9723…`, 129,231,128 bytes, `--version` → `simple-bootstrap
1.0.0-beta` rc=0), on the same hand-written two-line file:

```
$ printf 'fn main():\n    print("hi")\n' > probe_tiny.spl
$ .../stage2/x86_64-unknown-linux-gnu/simple native-build \
    --target x86_64-unknown-linux-gnu --backend llvm -o ./tiny probe_tiny.spl
[lexer_fatal] dead lexer: ... for path 'probe_tiny.spl' at line 1 col 1;
source length 27. Terminating token stream at EOF.
Segmentation fault (rc=139)
```

`source length 27` and `source length 21918` both **match the real file sizes**,
so file reading is fine — as the previous analysis correctly concluded. Only the
lexer's own state is lost.

### Revised root-cause hypothesis (NOT yet proven — do not treat as settled)

`line 1 col 1`, `cur_kind 0`, `cur_text ""` and `pos 0` are **exactly and
entirely** the `make_core_lexer` constructor defaults (`lexer_struct.spl:167-180`:
`pos: 0, line: 1, col: 1, cur_kind: 0, cur_text: ""`). That the *return value* of
`next_token()` is also 0 points away from "the mutation is not visible to the
caller" and toward a stronger claim:

> **`var loaded = current_core_lexer_slot[0]` — reading a value-type struct out
> of a module-level array slot under Stage-2 native codegen — yields a
> DEFAULT/zeroed `CoreLexer`, not the stored one.**

`next_token()` would then be scanning a lexer with `source == ""` and correctly
returning "nothing here" for a file whose bytes are present elsewhere. This
reframes the defect as a **native-codegen struct-in-module-array read bug**, not
a lexer bug — which is consistent with the known family
(`reference_native_list_rebind_and_spill_miscompiles`,
`reference_native_dict_get_struct_corrupt_len_minus_one`). Deliberately not
fixed here: confirming it needs a minimal codegen repro (store a struct in a
module-level `[T]`, mutate via a `me` method, read it back in another function),
and guessing at a compiler-codegen fix is exactly the wrong move.

### Sibling audit (the item listed as "not done" below) — DONE, and it found more

Swept `src/compiler/**` + `src/lib/**`: 4278 `struct` vs 3179 `class` decls,
~71 k candidate call sites, 68 read-back sites (49 unique) within 5 lines of a
mutating method call. **All 49 resolve to `class` receivers** (reference
semantics — not the defect). The **only** struct-receiver instances are in
`lex_next()` itself, i.e. the very function that was patched, on the fields the
patch did *not* touch:

- `lexer.spl:608` `loaded.cur_start`, `609/613` `loaded.pos`,
  `610` `loaded.cur_no_interp`, `615/619` `loaded.cur_text`.

Corroboration that these reads are already known-unreliable: the same function
deliberately avoids `loaded.cur_line`/`cur_col`/suffix, using the module-global
mirrors `core_lexer_last_line_get()` / `_col_get()` / `_suffix_get()` instead
(lines 616-621). `core_lexer_last_text_get()` exists and is exported
(`lexer_struct.spl:113, 1689`) yet line 615/619 still read `loaded.cur_text` —
an inconsistency, not a design choice. `cur_start`/`pos`/`cur_no_interp` have no
mirror at all. Under the revised hypothesis these are all moot until the struct
read itself is fixed, but they must not be left as-is.

### THIRD defect: the strengthened gate is STILL fail-open — root cause found

The gate passed a binary that cannot compile a two-line file. Evidence file
`stage3/x86_64-unknown-linux-gnu/stage2-sanity.env`:

```
status=pass
frontend_smoke_status=0
frontend_smoke_bootstrap_mode_status=0        # the NEW both-modes check
frontend_smoke_output_sha256=e3b0c442…852b855  # sha256 of the EMPTY string
```

Both `SIMPLE_BOOTSTRAP` modes ran and both produced **zero bytes** of output —
so the `[lexer_fatal]` / `Unknown(0) ''` rejection at
`candidate_frontend_admission.shs:77-79` had nothing to match, and the 4 MiB cap
was never approached. The checks are correctly written; they are never reached.

Cause: `candidate_frontend_admission.shs:61` invokes the candidate as
`native-build --entry <fixture>`. **`--entry` delegates to the Rust runtime**
(known trap: `reference_entry_flag_delegates_to_rust_runtime`,
`reference_entry_flag_stage3_selfhost_regression`), so the candidate's **own
pure-Simple frontend is never exercised**. Stage 3, by contrast, passes the
source positionally.

Proved on the same binary, same fixture, A/B:

```
A (gate's form):  simple native-build ... --entry p2_add.spl
   -> rc=0, "Build complete: 1 compiled, 0 cached, 0 failed", ./a_entry prints 5
B (Stage 3 form): simple native-build ... p2_add.spl
   -> rc=124 (TIMEOUT at 90 s), 0 bytes of output
```

A green gate and a hung compiler, from one binary, separated only by `--entry`.
**Fix: the smoke must invoke the candidate the way Stage 3 does — positionally,
without `--entry` — and must enforce a wall-clock timeout** (case B produced *no*
output at all, so an output-pattern check cannot catch it; only a timeout can).
This is the same fail-open class as the original gate defect and is arguably the
most important finding of the run: without it, every future dead-frontend
regression is admitted to Stage 3 again.

### Runaway safety — the landed mitigations WORKED, and were still not enough

The forward-progress invariant + fail-closed guard did what they were built to
do: `stage3-native-build.log` was **195 bytes / 1 line**, versus
**444,103,752 bytes / 6,299,344 lines** before. No disk risk. Keep both changes.

**However, memory still ran away with the log bounded.** The Stage-3 process
(`stage2-admitted/simple native-build … bootstrap_main.spl`) climbed
27.8 GB → 33.8 GB → 40.8 GB → **44.3 GB RSS in under 4 minutes** while emitting
nothing further. It was killed deliberately at 12:57-12:58 (host recovered to
96 G available, 1.3 T free). So a log-size gate is **not** a sufficient runaway
detector for this failure — RSS must be watched too. Watchdog used:
`/home/ormastes/dev/pub/bootstrap_out_20260809/wd2.sh` (30 s sampling; kills on
>200 KB/s log growth, >2 GB logs, >48 GB single-process RSS, <8 G RAM, <50 G disk).

### Consequence for the nil-receiver SIGILL bug — still blocked, unchanged

Blocker 12 is **not** cleared. Stage 3 again never got past lexing its entry
file. Over the whole run: `[mir-stmt-caller]` = 0, `garbage-expr` = 0,
`field access on nil receiver` = 0, `SIGILL`/exit 132 = 0 — both probes were
enabled and both produced nothing, because the fault site never executed. The
2026-08-05 bug remains **UNVERIFIED**, neither confirmed nor refuted.

## Not yet done

- **No full bootstrap was run after the fix.** The fix is verified through the
  interpreter path only. Confirming it on a freshly-built Stage-2 binary — and
  thereby finally reaching the nil-receiver SIGILL fault site in
  `stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md` — is
  the outstanding step.
- **Sibling audit not done.** `lex_next()` was one instance of "mutate a
  value-type struct through a `me` method, then read a field back off it". Other
  `me`-mutation-then-field-read-back sites in `src/compiler/**` may carry the
  same defect and should be swept; prefer returning the value.
- The pure-Simple parser accepts a bare `@@@` module body without error
  (`parse_module_silent_checked` returns false) while the Rust seed rejects it.
  Found incidentally while writing the regression spec; unrelated to this bug
  and not tracked elsewhere yet.

## 2026-08-09 run 5 — ROOT CAUSE FOUND. The codegen hypothesis is REFUTED.

Status change: the "native-codegen loses a value-type struct in a module-level
array slot" hypothesis from run 4 is **disproven by direct measurement**, and the
actual defect — which reproduces **in the interpreter, with no bootstrap at all**
— has been found and fixed in `lexer_struct.spl`.

### Part 1 — the codegen hypothesis, refuted by four repros

All four were built with the **exact** compiler and flags that produce Stage 2
(`stage2-runtime-authority` seed, `--backend llvm --runtime-bundle
core-c-bootstrap --entry-closure --mode dynload`, `SIMPLE_NATIVE_BUILD_RUST=1
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BOOTSTRAP=1`), and run natively. Every one
printed identical, correct values under the interpreter and under native:

| # | pattern | native result |
|---|---------|---------------|
| 1 | struct in module-level `[T]`, assigned in fn A, read in fn B, `me` method mutates, field read back, stored back, reloaded | **correct** (41→42 throughout) |
| 2 | same, with `SIMPLE_BOOTSTRAP=1` + `--mode dynload` | **correct** |
| 3 | same, struct + `impl` in a **separate module** from the slot | **correct** |
| 4 | **nested** `me` mutation — `next_token()`→`scan_token()`→`make_token()` sets `self.cur_kind`, exactly the real shape | **correct** (42 at all three levels and on read-back) |
| 5 | `source.chars()` stored in a `[text]` struct field; `at_end()`/`peek()` off `.len()` | **correct** (24 chars, `peek()=='f'`) |

Conclusion: **(a) the array index read, (b) the method call's in-place mutation,
and (c) local-variable aliasing are all fine.** The answer is (d), something
else — and it is not in the backend at all.

### Part 2 — the real defect: the ONE no-token return path in the scanner

`CoreLexer.handle_indentation()` (`lexer_struct.spl:1210`) had a bare

```
        if is_end:
            return
```

reached when EOF arrives while consuming a line's indentation. It emits **no
token**, so `self.cur_kind` keeps whatever it already held — and on the **first**
token of a file that is the `make_core_lexer()` constructor default **0**.
`next_token()` then returns 0. This is the only path in the whole scanner that
returns without routing through `make_token()`, and it produces **every**
observed symptom at once: `kind 0`, `cur_text ""`, and `line 1 col 1` (the
module-global mirrors `core_lexer_last_line_get()`/`_col_get()` are only written
by `make_token`, so they too read back as untouched defaults) — while
`current_core_source_get()` still reports the correct source length, exactly as
the run-4 evidence showed.

Reproduced with **`bin/simple run` in the interpreter**, no bootstrap, no
Stage 2:

```
$ cat probe2.spl
use core.lexer.{lex_init, lex_next}
fn main():
    lex_init("   ")
    print("first_kind={lex_next()}")

$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe2.spl
[lexer_fatal] dead lexer: next_token() produced kind 0 (never a valid token kind)
for path '' at line 0 col 0; source length 3. Terminating token stream at EOF.
first_kind=190
```

That is the run-4 diagnostic, verbatim, from three space characters. The
fail-closed guard landed in the previous campaign is what turns it into `190`
instead of a runaway — the guard works, and it is what made this findable.

### The fix

`handle_indentation()` now clears `at_line_start` and re-dispatches through
`scan_token_rescan()`, whose `at_end()` branch emits the pending dedents and the
real EOF token:

```
        if is_end:
            self.at_line_start = false
            self.scan_token_rescan()
            return
```

Termination is guaranteed: `at_line_start` is false on re-entry, and
`scan_token()` tests `at_end()` before any indentation handling.

### Evidence

- **New regression spec**
  `test/01_unit/compiler/frontend/lexer_indentation_eof_emits_token_spec.spl` —
  `SPEC FILE VERDICT ... declared>=6 executed=6 passed=6 failed=0 dropped=0`.
  Covers whitespace-only, tab-only, mixed-whitespace and empty sources (all must
  yield 190, never 0), plus two non-vacuity controls that a healthy program
  still lexes to a full stream ending in EOF.
- Before the fix, `first_kind_of("   ")` emitted `[lexer_fatal]`; after, it is
  190 with no diagnostic. Direct A/B on the same interpreter.
- No regressions: `lexer_dead_stream_forward_progress_spec` 5/5,
  `lexer_position_unification_spec` 4/4.

### What is still open

- **Not yet proven end-to-end.** No full bootstrap has been run since this fix,
  so it is not yet established that this single path is the *whole* cause of
  Stage 2's failure on `bootstrap_main.spl` (that file does not begin with
  whitespace, so the trigger must be reached mid-scan — plausible via
  `advance()`/rescan, but unverified). It IS proven to be a real defect that
  produces the exact signature. The next campaign should re-run the bootstrap
  and, critically, land the run-4 gate fix first (drop `--entry` from
  `candidate_frontend_admission.shs`, add a wall-clock timeout) so a recurrence
  cannot be admitted to Stage 3 again.
- The run-4 sibling-audit items (`lexer.spl:608-619` reading `loaded.cur_start`
  / `pos` / `cur_no_interp` / `cur_text` back off the struct) are **not**
  defects — repro 4 proves those read-backs are sound. The inconsistency with
  the `core_lexer_last_*_get()` mirrors is cosmetic, not load-bearing.
- The strengthened admission gate is **still fail-open** via `--entry`. Unchanged
  from run 4 and still the highest-value remaining fix.

## 2026-08-09 run 6 (SIXTH campaign) — FIX VERIFIED END-TO-END

Assigned action: one genuine complete bootstrap-from-scratch at a tree
containing `d37b5e578b4`, to decide whether the interpreter-only proof holds in
a real Stage-2/Stage-3 chain.

Checkout: `git archive 51115402161 | tar -x` + alternates + `update-ref` +
`read-tree` (112,297 files). Host at launch: load 7.7, 1.2 T free on `/`, 71 G
RAM available. Both MIR probes enabled. Watchdog sampling log growth **and**
process-tree RSS every 15 s, scoped to this run's PID tree only (two sibling
sessions were running their own bootstraps concurrently).

### Run A — pristine `origin/main`: blocked before the lexer could be tested

Stage 2 failed at **link**, exit 1, ~3 min, 9 undefined symbols, no binary
produced. Root-caused and causally isolated to `36673b6b6a3` in
`stage2_native_build_link_undefined_method_symbols_2026-08-09.md`. This run
could say nothing about the lexer.

### Run B — same tree, `36673b6b6a3` reverted: the lexer fix HOLDS

```
Linked: .../stage2/x86_64-unknown-linux-gnu/simple (126002 KB) via clang++
Build complete: 809 compiled, 0 cached, 0 failed
  Stage 2: running bootstrap compiler sanity
  Stage 2 native-build capability passed
Stage 3: stage2 → bootstrap_main.spl (self-host)
Segmentation fault (core dumped)
```

**The dead-lexer signature is gone.** Evidence, not inference:

1. `grep -c lexer_fatal` over the whole run log **and** every per-stage log:
   **0**. Run 4's `[lexer_fatal] dead lexer: next_token() produced kind 0 ...
   for path 'src/app/cli/bootstrap_main.spl'` does not appear.
2. The Stage-3 crash backtrace (from the core dump) is
   `flat_ast_to_module` ← `parse_and_build_module_scoped` ←
   `parse_full_frontend_with_scope` ← `CompilerDriver.parse_all_impl`. That
   frame is reached **only after** the lexer and parser have produced a flat AST
   for the file. A binary that "reads every source as empty" cannot get there.
3. No unbounded parser-error loop, no exploding log (whole run log: 1,421 bytes
   — run 4's runaway was 444 MB), no runaway RSS (peak 2.6 GB for the entire
   process tree, versus 44 GB climbing in the earlier runaway).

The fail-closed guard and forward-progress invariant landed earlier are still in
place and still correct; nothing regressed.

### Caveat

Run B's Stage-2 binary was built with `36673b6b6a3` reverted, since pristine
`origin/main` cannot link Stage 2 at all. The lexer fix is verified on the
nearest buildable tree, not on a pristine one. That caveat disappears once the
Stage-2 link regression is fixed, and it does not weaken the conclusion here:
the reverted commit is a Rust-seed LLVM codegen change with no relationship to
`CoreLexer.handle_indentation()`.
