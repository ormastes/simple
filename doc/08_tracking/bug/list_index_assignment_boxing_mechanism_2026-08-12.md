# `list[idx] = value` bracket-assignment boxing mechanism — differential findings

**Status:** OPEN — one distinct, reproducible defect confirmed and localized
(callee-parameter-type-driven corruption); sha3.spl's continuing corruption is
NOT explained by that defect (sha3.spl is already fully `[i64]`-typed) and
remains unexplained after this session's isolation attempts. Read-only
investigation — no source files were edited by this session.
**Companion docs:** `sha256_core_value_tagging_corrupts_live_digests_2026-08-11.md`,
`sha3_untyped_list_boxing_corrupts_digests_2026-08-12.md`.
**Engine:** `bin/simple --version` reports the Rust-seed bootstrap binary
(`Simple Language v1.0.0-beta`, seed warning banner). All probes below ran via
`bin/simple <file>.spl` on this seed. Some probes printed
`[INFO] JIT compilation failed, falling back to interpreter` (interpreter
lane); others did not (JIT lane, presumably Cranelift). This is noted per
probe below — **which engine actually executes `sha3_256_bytes` was not
conclusively determined this session** (the real-code invocation printed no
fallback message, suggesting JIT, while several passing synthetic probes also
ran on JIT with no fallback — so engine alone does not distinguish
pass/fail here).

## Confirmed real-world state (2026-08-12, this session)

`src/lib/common/crypto/sha3.spl` (unmodified, current `main`) has **already
had every relevant `list` annotation retyped to `[i64]`** — function params,
returns, the context tuple `([i64],[i64],i64,i64)`, and internal locals
(`state`, `buffer`, `s`, `c`, `d`, `b`, `out`, `tmp`) all carry explicit
`[i64]` annotations (verified by direct read of the file, lines 46-382).
Despite this, running it still reproduces the corruption from the companion
bug doc:

```
use std.crypto.sha3.{sha3_256_bytes}
sha3_256_bytes([97, 98, 99])
# Actual:   [240, 70, 0, 0, 0, 0, 0, 0, 17, 228, 2, 36, 62, 5, 0, 0,
#            33, 228, 2, 36, 62, 5, 0, 0, 49, 228, 2, 36, 62, 5, 0, 0]
# Expected: [58, 152, 93, 167, 79, 226, 37, 178, 4, 92, 23, 45, 107, 211,
#            144, 189, 133, 95, 8, 110, 62, 157, 82, 91, 70, 191, 226, 69,
#            17, 67, 21, 50]
```

Same repeating-byte-group signature as filed
(`207,148,205,4`-style / here `228,2,36,62,5,0,0`-style repeats every 4
output bytes after the first two lanes) — this rules out the
`sha3_untyped_list_boxing` doc's own "reverted, unchanged" caveat: whatever is
in `main` right now (fully `[i64]`-typed) is what was tested, and it is still
broken. The doc's suspected culprit ("bracket index-assignment... does not
propagate `[i64]` element-type tracking the same way `.push()` does") is
**not confirmed by this session's isolation attempts** — see below.

## Interpreter locus for `arr[idx] = value` (tree-walk lane)

`src/compiler_rust/compiler/src/interpreter/place.rs` is the assignment
l-value ("place") resolver for the tree-walk interpreter — this is a
DIFFERENT code path from whatever `.get()`/`Array::get` uses for reads.
Relevant functions:

- `resolve_place` (line 69) — evaluates `Expr::Index { receiver, index }`
  once into a `Place { root, projections: Vec<Projection> }`, pushing
  `Projection::Index(index_val)` (line 99-103).
- `project_mut` / `step_mut` (lines 138, 169) — walks projections to get a
  `&mut Value` for read-modify-write style access.
- `store_last` (line 182) — the actual write: for
  `(Value::Array(items), Projection::Index(index))` (line 192) it does a
  plain `normalize_index` + direct `items[i] = value` assignment — no
  special boxing/tagging logic is visible in this function for the
  `Value::Array` case. `Value::ByteArray` (line 199) and
  `Value::FixedSizeArray` (line 213) have their own arms; `Value::Tuple`
  (line 220) and `Value::Dict` (line 227) also have direct arms.
- `write_place` (line 245) / `updated_root` (line 285) — apply a `store_last`
  result back into the environment root, handling module-global sync
  (`sync_module_global`, line 267).

**This function reads as a plain, un-boxed, direct-indexing write path for
`Value::Array`** — nothing here re-tags or re-boxes the stored `Value`. This
is consistent with this session's finding that plain index-assignment,
even with function-call index expressions, nested nested nested loops, and
tuple-destructured typed locals, all round-trip correctly (see probes below).
The interpreter's read side (`.get()`/`step_ref`, line 296-305) was **not**
audited this session — the sha256 doc's finding was specifically about
`.get()` corrupting on arithmetic after an untyped-list read, and that is a
different function (`step_ref` here, or whatever `.get()` as a method call
actually dispatches to — not traced this session, flagging for next
investigator: confirm whether `.get()` on `Value::Array` goes through
`step_ref` at all, or through a separate method-call intrinsic in
`interpreter/expr/collections.rs` or `interpreter/expr/calls.rs`).

## Differential probes (all run `bin/simple <file>.spl`, seed binary)

All probes at
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/c934f8cd-84cf-4f01-9641-785d405efded/scratchpad/probe_*.spl`
(scratch, not committed).

### (a) untyped-list index-assign, literal RHS, no reads — PASS
```
var s = [0, 0, 0, 0]
s[0] = 999
s[2] = 0x6a09e667
```
`s.get(0)+5 == 1004` (correct), `s.get(2)+5 == 1779033708` (correct). Ran via
interpreter fallback (`[INFO] JIT compilation failed...` printed).

### (b) untyped-list index-assign, RHS reads+XORs another list's element — PASS
```
var s = [0x6a09e667, 0xbb67ae85, 0, 0]
var d = [0x11111111, 0x22222222]
s[2] = s.get(0) ^ d.get(0)
```
`s.get(2) == 2065233782` — matches `0x6a09e667 ^ 0x11111111` exactly.
Interpreter fallback.

### (c) same as (b), both arrays retyped `[i64]` — PASS, identical result
No behavior change from (b). Interpreter fallback.

### (d) same-file function-call boundary, UNTYPED callee param mutated via bracket-assign — **FAIL**
```
fn mutate(s):
    s[2] = s.get(0) ^ s.get(1)
    s
fn main() -> i64:
    var s = [0x6a09e667, 0x11111111, 0, 0]
    val out = mutate(s)
    print "{out.get(2)}"   # expect 2065233782
```
**Result: `r2=nil`, `r2+5=1`.** No JIT-fallback message printed (JIT lane).
This is a genuine, distinct corruption: not a shifted/tagged integer like the
sha256 family, but an outright decode failure to `nil`.

### (d2) same as (d), callee param AND return explicitly typed `[i64]` — PASS
Identical code with `fn mutate(s: [i64]) -> [i64]:` — correct result
(`r2=2065233782`).

### (d3) caller list UNTYPED, callee param/return TYPED `[i64]` — PASS
Mismatched declared types across the call boundary; callee's own annotation
governs. Correct result.

### (d4) caller list TYPED `[i64]`, callee param UNTYPED — **FAIL**, same as (d)
`r2=nil`, `r2+5=1` — identical failure to (d) even though the caller's local
was declared `[i64]`.

**(d)/(d2)/(d3)/(d4) together pin the mechanism precisely: whether
bracket-index-assignment inside a function corrupts on read-back is governed
by that function's OWN declared parameter type for the array being mutated
— not by the caller's declared type, not by the actual runtime list
contents.** An untyped `list` parameter that is bracket-assigned inside its
own function body reliably decodes to `nil` on a later `.get()`, regardless
of how it got there. This is a real, narrow, mechanically distinct defect
from the sha256 `.get()`-arithmetic tagging bug (that one silently
mis-decoded to a wrong *number*; this one decodes to `nil`).

### (f) fully `[i64]`-typed throughout, index expr is itself a function call, nested double while-loops, writing into a SEPARATE array from the one read (mirrors keccak_f1600's ρ+π step) — PASS
```
fn lane_idx(x: i64, y: i64) -> i64: x + y * 5
fn rotl(v: i64, n: i64) -> i64: v ^ n
fn step(s: [i64]) -> [i64]:
    var b: [i64] = [0,0,0,0,0,0,0,0,0,0]
    while y < 2: while x < 2:
        val idx = lane_idx(x, y)
        val rotated = rotl(s.get(idx), 1)
        b[lane_idx(y, x)] = rotated
    b
```
Both spot-checked outputs correct (`10^1=11`, `70^1=71`).

### (g) tuple-param destructure `ctx[0]` (bracket-index on a TUPLE) assigned into a typed `[i64]` local, then bracket-assigned — PASS
```
fn mutate_ctx(ctx: ([i64], i64)) -> [i64]:
    var state: [i64] = ctx[0]
    state[1] = state.get(0) ^ 0x11111111
    state
```
Correct (`r1=2065233782`), matching sha3_update/finalize's
`var state: [i64] = ctx[0]` pattern exactly — this shape is not the culprit
either.

## What this rules in / rules out

**Ruled IN (real, confirmed, reproducible defect):** a `list`-typed (untyped)
function PARAMETER that is bracket-index-assigned inside that function's own
body corrupts to `nil` on later read, independent of caller typing. Locus:
some divergence between how the JIT (or interpreter, for probe (a)/(b)/(c))
binds/tags an untyped-`list`-typed parameter slot versus a `[i64]`-typed one,
surfacing specifically when that slot is later used as a bracket-assignment
LHS. `place.rs`'s `store_last`/`Value::Array` arm itself is type-agnostic
Rust code with no visible special-casing, so if this is an interpreter-lane
bug it is more likely upstream — in how the parameter binding step
constructs/tags the `Value` before `place.rs` ever sees it — not in
`store_last` itself. Not localized to a specific Rust function this session;
`interpreter/expr/calls.rs` (function-call/parameter-binding) is the
strongest next lead, not yet read.

**Ruled OUT as the sha3.spl explanation:** sha3.spl is **already fully
`[i64]`-typed** everywhere (verified 2026-08-12 read of current `main`), so
the "ruled IN" defect above (untyped parameter) cannot be what's corrupting
it — there is no untyped list parameter left in the file for that mechanism
to trigger on. Every individual sub-shape this session could think to extract
from `keccak_f1600`/`sha3_update`/`sha3_finalize` — function-call index
expressions, nested double while-loops writing cross-array, tuple-param
destructuring into a typed local — reproduces CORRECTLY in isolation with
full `[i64]` typing. sha3.spl's corruption must therefore come from either:
(a) call-depth/compounding across many hops, matching the sha256 doc's
explicit finding that "reboxing at any single hop does not neutralize
corruption introduced at a different hop" and that direction/magnitude of
corruption compounds and flips sign with depth — `keccak_f1600` alone is 24
rounds × ~5 helper-call sub-steps, far deeper than any probe here reached; or
(b) some other shape not yet isolated (e.g. the specific combination of ALL
these things simultaneously, or the cross-module `use std.crypto.types.{rotl64}`
scalar call crossing 24×5 times, which was not isolated at this call depth
this session).

## Next steps for whoever picks this up

1. Read `interpreter/expr/calls.rs`'s parameter-binding path to see whether
   untyped-`list`-typed parameters get a different `Value` construction/tag
   than `[i64]`-typed ones — that is the most direct lead from this session's
   (d)/(d4) finding, and unlike sha3 it is a SMALL, fully isolated repro.
2. For sha3.spl specifically: build a probe that repeats probe (f)'s
   correctly-passing shape for many more iterations (e.g. 24 rounds, not one
   step) to test the call-depth-compounding theory directly, since no
   single-round isolation failed here.
3. Confirm which engine (JIT vs interpreter) actually executes
   `sha3_256_bytes` in the real `use std.crypto.sha3.{...}` invocation —
   not conclusively determined this session (no fallback message printed,
   unlike several of the synthetic probes).
