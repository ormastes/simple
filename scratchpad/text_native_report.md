# Text/String Support on the Native `--entry` Path — Characterization Report

Worktree: `/tmp/wt_textnat` @ `35c4b52ead636edda2f2c8f9706ede0abb86d8e5`
Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (confirmed to be the **Rust seed**, not a
self-hosted binary — it prints "this Rust-built Simple binary is a bootstrap seed only" on every
invocation).

## TL;DR

This exact pinned commit's `native-build --entry` path was **100% broken for every program**,
including trivial arithmetic (`fn main() -> i64: return 0`) — not specific to text/strings at all.
Root-caused and fixed one blocker (unrelated to text, in `lexer_struct.spl`). Hit a second,
already-known/owned blocker (missing native extern in the currently-deployed seed binary) that
requires a shared seed rebuild — out of this task's scope, and explicitly tracked elsewhere in
project memory as another lane's in-flight work. Because of blocker #2, **no native-path
dynamic verification of text/string constructs was possible** this session; the smoke matrix
still reads 0/15 (blocked at frontend init on every case, confirmed universal, not text-specific).

## Characterization: oracle (interpreter) — ALL CORRECT

`env -u SIMPLE_BOOTSTRAP bin/simple run <probe>.spl` for all 6 requested probes:

| # | Construct | Program | Oracle output | Verdict |
|---|-----------|---------|----------------|---------|
| 1 | interpolation, text var | `val name="world"; print("hello {name}")` | `hello world` | CORRECT |
| 2 | interpolation, int+expr | `val n=42; print("n={n} n2={n*2}")` | `n=42 n2=84` | CORRECT |
| 3 | concat + `.len()` | `"abc"+"def"` then print + `.len()` | `abcdef` / `6` | CORRECT |
| 4 | `.contains()` | `"abcdef".contains("cd")` in `if` | `YES` | CORRECT |
| 5 | `.replace()` | `"a,b".replace(",", "-")` | `a-b` | CORRECT |
| 6 | `==`/`!=` | `a==b`, `a!=c` | `EQ_OK` / `NEQ_OK` | CORRECT |

No interpreter-level bugs found for any requested construct.

## Native path: baseline verification (before touching text at all)

Before running the 6 text probes natively, I ran a **plain arithmetic baseline**
(`write_case_arith` from `scripts/check/native-smoke-matrix.shs`: `add(3,4)` returning `7`) through
`native-build --entry` to sanity-check the harness. It failed identically to every other case:

```
error: semantic: type mismatch: cannot cast array to i64
```

Running the full `scripts/check/native-smoke-matrix.shs` confirmed **all 13/15 cases that ran
before the shell timeout also failed identically** (`build-failed`, 0 codegen fallback hits) —
this is a universal pipeline blocker, not a text-specific one. This changed the shape of the task:
before any text-specific work was possible, the native `--entry` pipeline itself had to be
unblocked.

### Root cause #1 (FIXED): `array as i64` reinterpret-cast in `lexer_struct.spl`

`bin/simple native-build` works by **interpreting** the whole `src/compiler/*.spl` pipeline as a
program (confirmed via `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1` phase tracing — the crash
happened on `phase2:parse:file:start`, inside `parse_and_build_module` → `lex_init_with_path` →
`core_token_env_save_set` → `rt_array_len_safe`, for literally every input, even before reaching
the user's `main`).

`src/compiler/10.frontend/core/lexer_struct.spl` (introduced by the exact pinned "sync: workspace
snapshot" commit `35c4b52ead6` itself — `git show 35c4b52ead6 --stat` shows this is the only `.spl`
file that commit touched) contained:

```simple
fn rt_array_len_safe<T>(array: [T]) -> i64:
    # ... comment about one-binary freestanding native builds ...
    val raw = array as i64
    if raw < 4096:
        return 0
    return array.len()
```

`array as i64` is a **native-codegen-only reinterpret** (valid only when `[T]` compiles down to a
raw pointer-sized register, e.g. a self-hosted binary or the SimpleOS freestanding kernel). The
seed's own interpreter models `[T]` as a genuine boxed `Value::Array` and hard-errors on the cast
with exactly `"semantic: type mismatch: cannot cast array to i64"`. Since this function runs on
**every single parse** during native-build's self-interpretation of the compiler pipeline, it broke
100% of native builds regardless of program content.

**Fix applied** (`src/compiler/10.frontend/core/lexer_struct.spl`, my file per the task's allowed
scope for string-literal-adjacent frontend paths — this one is upstream of them and blocked
everything):

```simple
fn rt_array_len_safe<T>(array: [T]) -> i64:
    if array == nil:
        return 0
    return array.len()
```

I first tried gating the risky cast behind `SIMPLE_EXECUTION_MODE == "interpret"` (a real,
established convention already used by `native_build_main.spl` for its worker subprocess), but
verified empirically (via temporary `eprint` tracing, since removed) that this env var reads back
as `nil` inside the native-build worker subprocess despite the parent explicitly setting it —
`env_set`/`rt_env_set` do not reliably propagate across the subprocess boundary here. Rather than
rely on an unverified propagation channel, I dropped the reinterpret-cast entirely and kept only
the nil-check, which is what the interpreter path actually needs. This drops protection for the one
narrow scenario the original comment described (zeroed-`.bss` uninitialized array globals in
one-binary freestanding/bare-metal builds) — out of this task's scope and not exercised by
`native-build --entry`; flagged below as a follow-up for whichever lane owns that freestanding
target.

Verified: after the fix, the arithmetic baseline and the interpolation probe both get **past**
frontend init and hit a different, later error (below) instead of the universal cast crash —
confirmed on 3 independent runs with uniquely-named source files (to rule out any object-cache
false negative).

### Root cause #2 (NOT FIXED — out of scope, already tracked): stale seed binary missing `rt_lexer_source_set`

After fix #1, every probe (arith baseline and the text probes alike) now fails later, still
universally, with:

```
error: semantic: unknown extern function: rt_lexer_source_set
```

Investigation: `rt_lexer_source_set` is called unconditionally at the end of
`parse_and_build_module` (`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:491`). Its
Rust-side interpreter implementation **does exist in this worktree's checked-out source**
(`src/compiler_rust/compiler/src/interpreter_extern/system.rs:184`, registered at
`interpreter_extern/mod.rs:1041`), and — like the lexer_struct.spl bug above — was added by the
exact same pinned "sync: workspace snapshot" commit `35c4b52ead6`. But the **currently-deployed
seed binary** (`bin/release/x86_64-unknown-linux-gnu/simple`, built 2026-07-11) predates this
commit (2026-07-13) and simply doesn't have this extern compiled in. This is a pure seed/source
version skew, not a logic bug — a rebuild of the seed from this worktree's source would resolve it.

This matches project memory almost exactly: *"Lexer O(n²) parse perf + native slice migration —
... via native rt_lexer_source_set/slice (in-flight, needs rebuilt seed) ... its slice is
BYTE-indexed vs char-based pos = latent unicode bug to file"* — i.e. this is **another lane's
active, in-flight work**, explicitly noted as blocked on a seed rebuild. I did not attempt the
rebuild myself: it's a shared-resource, ~11GB-target, potentially 15–45+ minute `cargo build`
under an already heavily-loaded shared machine (dozens of concurrent `git log`/`worktree add`
processes were observed at 90%+ CPU each throughout this session), it risks colliding with the
owning lane's in-progress fix, and it is explicitly out of this task's scope (I was told to use the
binary as symlinked, not rebuild it).

**Consequence for this task:** because blocker #2 is hit on every single program (confirmed by
re-running the arith baseline and the `t1_interp_var` interpolation probe — both fail identically
at the same point), **no native-path dynamic verification of any text/string construct was
possible this session**, string-specific or otherwise. The oracle characterization above (all 6
constructs CORRECT under the interpreter) stands as the semantic reference; I could not confirm or
deny native-path correctness for interpolation, concat, `.len()`, `.contains()`, `.replace()`, or
`==`/`!=` beyond what prior sessions already established, because the pipeline never got far enough
to reach HIR/MIR lowering for **any** program, text or otherwise.

## CONFLICT-FLAGGED / follow-up items

1. **Freestanding zeroed-global protection removed from `rt_array_len_safe`.** The narrow
   "one-binary freestanding native build reads an uninitialized array global as a raw `0` handle"
   scenario (per the original comment, mirrored in `src/os/libc/simpleos_libc.c`) is no longer
   guarded in `lexer_struct.spl`'s `.spl`-side helper. Proposed longer-term fix (not applied,
   needs the owning SimpleOS/freestanding lane's judgment): give that target its own
   `rt_array_len_safe_freestanding`-style helper gated by a real compile-time target signal (e.g.
   a working `@cfg` dimension), rather than sharing one function across both the always-interpreted
   native-build worker path and the freestanding kernel-codegen path. `@cfg` was avoided here
   because project memory flags an active "@cfg multivariant misdispatch" bug — using it without
   that fix landed would risk silently picking the wrong variant.
2. **Seed rebuild needed for `rt_lexer_source_set`/`rt_lexer_source_slice`.** Already owned per
   project memory ("Lexer O(n²) perf + native slice migration" project note). Recommend re-running
   the full text/string native characterization (this task) once that rebuild lands — at that
   point the pipeline should get far enough to reach HIR/MIR lowering and actually exercise
   interpolation/concat/`.len()`/`.contains()`/`.replace()`/`==` codegen.
3. Given #2, **`scripts/check/native-smoke-matrix.shs` still reads 0/15** (all `build-failed`,
   0 codegen-fallback hits) — this is unavoidable until the seed rebuild lands; not a regression
   from this session's fix (fix #1 measurably moves every case past frontend init to a later,
   shared failure point, which is progress, but not enough to flip any case to PASS yet).

## Files touched

- `src/compiler/10.frontend/core/lexer_struct.spl` — real fix (root cause #1), see patch.
- Patch: `/home/ormastes/dev/pub/simple/scratchpad/text_native.patch`
- No other files modified; worktree cleaned (`probes_local/` scratch dir removed) before diffing.

## Recommendation

1. Land the `lexer_struct.spl` fix (or an equivalent) — it is a genuine, verified, minimal,
   text-agnostic correctness fix for the interpreted native-build path, independent of this task's
   original text/string mandate.
2. Do not attempt further text/string native-path fixes or the smoke matrix gate until the seed is
   rebuilt with `rt_lexer_source_set`/`rt_lexer_source_slice` support (owned elsewhere per project
   memory) — anything "fixed" before that point cannot be dynamically verified and risks exactly
   the silent-wrong outcome this task was meant to prevent.
3. Once unblocked, re-run this task's 6-probe matrix plus the multi-construct combined program and
   the full smoke matrix (gate ≥14/15, 0 fallback hits, only `option_nil_check` XFAIL) as originally
   specified.
