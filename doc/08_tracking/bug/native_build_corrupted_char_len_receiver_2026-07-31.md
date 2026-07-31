# `native-build` phase2:parse: `.len()` on identifier `c` receives a corrupted `str` (renders as U+FFFD) — localized, not fixed

**Status:** localized to file + call-site identifier + exact position in the
driver's parse sequence; root byte-provenance NOT found; no fix attempted
(does not look trivially contained). Follow-up to
`doc/08_tracking/bug/native_build_direct_seed_jit_hang_2026-07-30.md`, whose
"Separate `<corrupted char>` receiver error" section flagged this as
worth its own investigation.

## Correction to the prior doc's transcript

The prior doc quotes the error as containing the literal text
`<corrupted char>`. That is **not** what the terminal printed — no such
string literal exists anywhere in this repo's Rust or Simple source (checked
by grep across the whole tree). The actual byte sequence, captured raw this
pass (`xxd` on the log line), is:

```
... 7661 6c75 653a 20ef bfbd 290a   value: ...).
```

`ef bf bd` is the UTF-8 encoding of **U+FFFD REPLACEMENT CHARACTER** — one
single glyph. `<corrupted char>` in the prior doc was the investigator's
paraphrase of an unprintable/replacement glyph in their terminal capture,
not literal program output. This matters because U+FFFD is exactly what
Rust's `String::from_utf8_lossy` emits for byte(s) that fail UTF-8
validation — a real, traceable mechanism, not a placeholder string.

## Reproduction (2 independent runs, byte-identical failure both times)

Direct worker invocation (bypasses `native_build_main.spl`'s output
buffering), per the standing recipe:

```
env SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_EXECUTION_MODE=interpret \
    SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1 SIMPLE_COMPILER_TRACE=1 \
    SIMPLE_INTERP_OOB_DEBUG=1 RUST_BACKTRACE=1 \
    SIMPLE_BINARY=<seed-binary> stdbuf -oL -eL <seed-binary> \
    run src/app/cli/native_build_worker.spl \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure --entry src/app/cli/bootstrap_main.spl \
    --backend cranelift -o <out> --verbose --timeout 3000
```

Run 1 (no extra tracing): entry-closure BFS (485 files) completes in ~9 min,
`[native-build] Driver start: inputs=485 backend=cranelift mode=dynload`
prints, then ~6 min later, with **zero** intervening output:

```
error: semantic: method `len` not found on type `str` (receiver value: <U+FFFD>)
```

Run 2 (`SIMPLE_COMPILER_TRACE=1 SIMPLE_INTERP_OOB_DEBUG=1`): same failure,
now fully attributable. Total wall clock ~24 min (worktree at
`refs/heads/main` clean tip `65ca4209476...`, host load 10-40 throughout
from unrelated concurrent sessions).

## Exact localization

**Confirmed engine-dependent: reproduces under `SIMPLE_EXECUTION_MODE=interpret`
explicitly**, both runs. Per the STRONG PRIOR in this investigation's brief
("check whether it reproduces under interpret too, since JIT/codegen
raw-value-misread defects are a documented family here") — it does. This
was *not* re-tested under default/JIT mode this pass: the sibling doc
(`native_build_direct_seed_jit_hang_2026-07-30.md`) already established that
a direct-seed `native-build` invocation under default mode hangs *before the
worker's `main()` is ever entered* — i.e. default mode never gets far enough
to reach this error at all, so re-running it would only re-confirm the hang,
not add JIT-vs-interpret signal for this specific defect. Treat "does this
reproduce under JIT" as still formally open, but low-value to chase without
first resolving the hang.

**Driver phase2:parse sequence** (`SIMPLE_COMPILER_TRACE=1`,
`[BOOTSTRAP-PHASE]` / `[frontend]` lines), in order, both fully parsed with
no error:

1. `src/app/cli/bootstrap_main.spl` (chars=15716) — the entry file
2. `src/compiler/driver/driver.spl` (chars=5517)
3. `src/compiler/common/driver_core_types.spl` (chars=823)
4. `src/app/cli/bootstrap_identity.spl` (chars=170)
5. `src/app/cli/bootstrap_focused_native_build.spl` (chars=5540)

Then the **6th** file:

6. `src/std/nogc_sync_mut/io_runtime.spl` (chars=10889) — `[frontend]
   parse_and_build:start path=...` prints, and the crash fires
   **immediately after**, with no intervening trace line and no
   `parse_and_build:done`. This is the "roughly 5 modules into the driver
   phase" signature from the investigation brief: 5 files completed, the
   6th never finishes.

`io_runtime.spl` itself contains **zero non-ASCII bytes** (checked directly,
`grep -P "[\x80-\xff]"` — no hits; `file` reports plain UTF-8/ASCII). So the
corrupted receiver is not simply "this file has weird content" — whatever
holds the bad byte(s) either came from earlier interpreter state carried
across the 5 prior files, or from a value built by the parser itself
(e.g. a path/module-name string, a synthesized token fragment) rather than
directly sliced from this file's source text.

**Call site, from the interpreter's own debug hooks**
(`SIMPLE_INTERP_OOB_DEBUG=1`, printed by
`src/compiler_rust/compiler/src/interpreter_method/mod.rs:1525-1531` and a
companion `[mnf-expr]` print at the call-expression evaluator):

```
[mnf-debug] method=len recv_type=str
[mnf-expr] method=len recv_expr=Identifier("c")
```

So the failing call is `c.len()` where `c` is a bare local/parameter named
`c` — the single-letter idiom used throughout this codebase for "one
character as a `text` value." The receiver's `type_name()` is `str`
(`Value::Str` or `Value::StrBytes` — both map to `"str"` per
`value_impl.rs:589-590`), confirming the interpreter's own tag says this
*is* a string, not some other type wearing a str-shaped error message. Its
`to_display_string()` (`value_impl.rs:397-401`) is:
```rust
Value::Str(s) => s.as_ref().clone(),
Value::StrBytes(b) => String::from_utf8_lossy(b).into_owned(),
```
Only the `StrBytes` arm can produce a lossy U+FFFD from invalid bytes (a
`Value::Str` is a Rust `String`/`Rc<str>`, which cannot hold invalid UTF-8
without `unsafe`). This makes `Value::StrBytes` holding non-UTF8 bytes the
leading candidate for the receiver's concrete variant, though not directly
confirmed (the "str" type_name alone doesn't disambiguate the two).

**Not found: a specific `.spl` line.** Grepped the whole `src/compiler` tree
for the exact pattern `\bc\.len()` (the receiver identifier is exactly `c`,
per the AST dump above) — the only hit is
`src/compiler/40.mono/monomorphize/deferred_subst.spl:109`, which is
**phase4 (monomorphize)**, not phase2 (parse) — doesn't match the observed
crash point. The single-character-slice idiom this bug's shape matches
(`val c = s[i:i+1]` then `c.len() != 1` / `c.len() == 0`) is common in
`src/app/io/sffi_common.spl`, its duplicated siblings under
`src/lib/*/io/sffi_common.spl`, `src/app/io/string_helpers.spl`, and
`src/lib/common/string_core.spl`'s `char_code_inline` — but none of those
are reachable from `parse_and_build_module_scoped`
(`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:698`) by
direct import, and `char_code_inline` specifically has **zero** call sites
anywhere in `src/compiler` (dead code). The interpreter's "method not
found" error path (`interpreter_method/mod.rs:1478-1563`) never calls
`.with_span(...)` on its `ErrorContext` — a separate, small, structural gap
that explains why no `.spl` file:line ever prints for this error class, not
specific to this bug. Pinpointing the exact source line needs either a
Rust-side patch adding span-tracking to that error path (small, contained,
but requires a seed rebuild+redeploy cycle — not attempted this pass) or
substantially more manual bisection within `parse_and_build_module_scoped`'s
call graph.

**A relevant, already-standing comment in this exact file**
(`src/compiler/10.frontend/core/lexer.spl:311-315`, directly above
`core_digits_to_i64`, itself a `val c = s[i:i+1]` single-char-slice
function): *"the seed interpreter misdispatches `.to_int()` on
`split()`-produced strings (and in plain assignment position) to a wrong
impl method, returning pointer-like garbage — which corrupted the indent
stack"*. This is an independently-documented instance of the same class of
defect in the same file (seed interpreter method dispatch returning garbage
for a String-typed receiver), giving structural support to "engine-side
value corruption reachable from the lexer", though not proof this specific
call site is the same one.

## Compiler defect or source defect?

**Compiler (interpreter) defect, not a source-level `.len()` misuse.** The
`.len()` call on `c` matches an idiom (`if c.len() != 1: ...` /
`if c.len() == 0: ...`) that is correct and common throughout this codebase
for validating a single-character text slice. Nothing in the reproduction
suggests the *call* is wrong; the receiver value delivered to it is wrong.
`type_name()` says `str` (the interpreter believes it produced a string),
but the content is invalid UTF-8 once rendered — that mismatch can only
originate engine-side: either a byte-oriented text-slice primitive
(`text[i:i+1]`-shaped) that doesn't respect UTF-8 character boundaries when
`i` lands mid-codepoint, or leaked/aliased interpreter state from a prior
file's processing (per the standing lexer.spl comment above). Both
candidates are structural, cross-cutting interpreter concerns, not
containable to one `.spl` edit — consistent with the task's instruction not
to force a fix here.

## Determinism

100% reproducible, byte-identical failure, same file (`io_runtime.spl`),
same position (6th in the phase2:parse sequence, immediately on entry, no
partial progress), across two independent runs on a clean `refs/heads/main`
worktree. Not a heisenbug — a specific, stable trigger condition tied to
having processed exactly the same 5 prior files first (source-set order is
itself deterministic — the entry-closure BFS discovery order is stable
given a fixed source tree, since it's driven by declared imports).

## Next steps for whoever picks this up

1. Add `.with_span(...)` to `interpreter_method/mod.rs`'s "method not found"
   `ErrorContext` (small, self-contained, Rust-side only) so a `.spl`
   file:line prints on every future occurrence of this error class —
   removes the need for ad hoc `SIMPLE_INTERP_OOB_DEBUG`/`SIMPLE_COMPILER_TRACE`
   bracketing to localize the next one.
2. With that in place, re-run this exact repro; the location will pinpoint
   the `.spl` call site directly instead of requiring the phase-boundary
   inference used here.
3. Independently instrument `Value::StrBytes` construction sites (or add a
   debug assertion that panics loudly, env-gated, when a `StrBytes` payload
   fails `str::from_utf8` at construction) to catch the corrupting write at
   its origin rather than at the `.len()` call several steps downstream.
4. Re-test under default (JIT) execution mode once the upstream hang
   (`native_build_direct_seed_jit_hang_2026-07-30.md`) is resolved enough to
   reach this point — currently blocked, not by this bug.
