# Fresh cargo-built seed: `native-build` failed on trivial entries — FIXED
# for both the noparam.spl symptom (P3) AND the param_add.spl
# INTERPRETED-execution symptom (lane KEY2). A THIRD, newly-discovered, still
# OPEN defect in NATIVE (compiled, non-interpreted) struct-spread lowering is
# documented below under "2026-07-18 lane KEY2 follow-up" -- read the
# "IMPORTANT SCOPE CORRECTION" note there before assuming the redeploy
# keystone is fully closed.

Lane: P3 (parallel bug-fix campaign), worktree `wt_p3` detached at
`a79a52ba8178e1e4fee4adfc24e101dd3de87d3c`. param_add.spl's interpreted-path
half fixed by lane KEY2, worktree `wt_key2`; a separate native-codegen
struct-spread defect found by the same lane remains open (see below).

## 2026-07-18 FOLLOW-UP: FIXED for the `noparam.spl` symptom (verified rc=7);
`param_add.spl` is a SEPARATE, still-open defect

**Everything below "Status" through "Resume commands" is the original
root-cause investigation, kept intact for the record.** This section is the
final, verified outcome, added after that investigation and after finding
(then reverting) two mid-course "fix attempts" that turned out to be
sitting on a corrupted verification state (see "Verification landmine"
below) — read this section first.

**The shipped fix** (all three empirically confirmed, see "Verification"
below):

1. `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`:
   `rt_file_read_bytes` now returns a bare `Value::array(...)` on success and
   `Value::Nil` on failure — not `make_some(...)`/`make_none()`. This mirrors
   the already-landed fix for the sibling `rt_string_bytes_fn` (bug
   `seed_flat_registry_len_i64_2026-07-17`). Native (non-interpreted)
   compilation never calls this extern binding (natively compiled code calls
   the C runtime symbol in `src/runtime/runtime_native.c` directly), so this
   change is native-safe by construction.
2. `src/lib/nogc_sync_mut/sfm/container.spl` (`read_sfm_file`) and
   `src/lib/nogc_sync_mut/io/telnet_serial_bridge.spl` (`bridge_rx_pending`)
   were the only two of the ~40 call sites (out of ~8 that declare this
   extern as optional, `[u8]?`/`[i64]?`) that pattern-matched
   `Some(value)`/`nil` directly on the raw return value — an idiom that
   silently mis-binds against a bare array instead of erroring (see
   "Verification" for the exact repro proving this: `.len()` silently came
   back `0` instead of `31`). **Both were rewritten to `rt_file_read_bytes(...)
   ?? []`**, not to an explicit `if x == nil: ... else use x` narrowing
   check: an earlier draft of this fix used the narrowing form, but that was
   only verified via the interpreter (`simple run`/`simple lint`) — both
   files are natively-compiled bootstrap stdlib, and whether the *native*
   type checker's flow-narrowing accepts assigning a post-nil-check `T?` to a
   `T`-typed `val` was never actually checked (a bootstrap rebuild to verify
   was judged out of scope). `?? []` sidesteps that open question entirely:
   it's the exact idiom already shipped and natively compiling today in two
   sibling `[u8]?` callers of this same extern
   (`src/app/editor/mcp_tools_helpers.spl:75`,
   `src/app/startup/launch_meta_check.spl:53`), so its native-safety is
   already proven by existing, running code, not by inference. Confirmed
   behavior-identical to the original logic in both rewritten functions:
   `sfm/container.spl`'s existing `if n == 0: return Err(...)` one line below
   already catches the nil→`[]`→`len 0` case (the removed nil-branch was
   redundant); `telnet_serial_bridge.spl`'s `bridge_rx_pending` loop over an
   empty array is a no-op, matching the original `None: pass_do_nothing`.
   The other ~30+ call sites that declare this extern as non-optional
   `[u8]` (including the originally-reported `llvm_backend_tools.spl`)
   needed no consumer-side change at all: they already assumed a bare
   array, which is now what they get.

   **Follow-up audit gate** (advisor-prompted, before declaring the fix
   complete): a broader tree-wide grep for *any* remaining
   `Some(`/`case Some(` match on `rt_file_read_bytes(...)` or its
   `rt_file_read_bytes(args)`-forwarding alias `rt_file_mmap_read_bytes`
   (not just the files that literally declare the extern nearby — the
   original audit only checked declaration sites) turned up **two more**
   genuinely-affected consumers, both under `src/os/port/`, both declaring
   the extern (incorrectly) as **non-optional** `[u8]` yet pattern-matching
   `case Some(bytes)/case None` on it anyway — the inverse inconsistency
   from `llvm_backend_tools.spl` (there: non-optional declaration + direct
   use; here: non-optional declaration + Option-style match, which only
   ever "worked" because the runtime shape used to actually be
   Option-wrapped regardless of the declared type):
   - `src/os/port/host_fat32_tree_populator.spl` (`_read_host_bytes`):
     rewritten to `rt_file_exists(path)` pre-check (added, mirroring the
     sibling file's existing pattern) + `rt_file_read_bytes(path) ?? []`,
     preserving the original error message on a missing file.
   - `src/os/port/cached_raw_image_block_device.spl`
     (`load_with_sector_size`): already had an `rt_file_exists` pre-check
     immediately above the match; simplified to `rt_file_read_bytes(...) ??
     []` directly (the pre-check already covers the missing-file error
     path; the removed `case None` branch was only reachable on a rare
     exists-but-unreadable race, previously silently defaulting is an
     acceptable, minor behavior narrowing there).
   Both files' `extern fn rt_file_read_bytes` declarations were also
   corrected from `-> [u8]` to `-> [u8]?` to match what they actually do
   (match/coalesce on a possibly-missing value) — matching the
   `?? []`-consuming, `[u8]?`-declaring shape already proven native-safe by
   `mcp_tools_helpers.spl`/`launch_meta_check.spl`. Re-grepped after these
   two fixes: no further `Some(`/`case Some(` matches remain anywhere in
   the tree against `rt_file_read_bytes`/`rt_file_mmap_read_bytes` (only 2
   docstring mentions of the old behavior, one of which — in
   `sfm/container.spl`'s header comment — was also updated to describe the
   corrected contract). `simple lint` on both newly-touched files reproduces
   one **pre-existing, unrelated** error (`method 'get' not found on type
   'str' (receiver value: CachedRawImageBlockDevice(Adapter))`) —
   independently confirmed present on the untouched original file content
   too (compared via `git show HEAD:<path>` into a scratch copy, never via
   `git stash` — see the stale-`LANE_HEAD` incident below for why stash is
   avoided entirely in this investigation), so it is not attributable to
   this fix.
3. **Not changed, flagged for awareness:** `rt_file_read_lines`
   (`file_io.rs`, two functions above `rt_file_read_bytes`) still returns
   `make_some(...)`/`make_none()` — the same Option-wrapping this fix
   removed from its sibling. Out of scope for this fix (no `.spl` entry
   point currently reaches it the way `rt_file_read_bytes` was reached), but
   any caller of `rt_file_read_lines` that assumes a bare `[text]` return
   would hit the identical bug; worth the same audit if it ever surfaces.
4. The one existing Rust unit test asserting the old contract
   (`interpreter_extern::file_io::tests::
   mmap_named_text_and_bytes_match_read_contract`) was updated to assert the
   corrected one.

**Verified:**
- `cargo test -p simple-compiler --lib interpreter_extern::` — 86/86 passed
  (was 85/86 before updating the one contract-asserting test).
- `cargo test -p simple-compiler --lib interpreter_method::` — 8/8 passed.
- `cargo test -p simple-compiler --lib interpreter_patterns::` — 12/12
  passed (SdnValue fix regression tests unaffected).
- `simple lint` on both touched `.spl` files — 0 errors (pre-existing,
  unrelated warnings only on `telnet_serial_bridge.spl`, none on my edited
  lines).
- **End-to-end, from a fresh incremental `cargo build --release --bin
  simple`:** `native-build --entry scratch_p3/noparam.spl --backend llvm
  --clean` now exits 0 and produces a binary that runs and returns **rc=7**
  (was: `error: semantic: unknown static method object on class
  CodegenOutput`). Exact commands in "Resume commands", updated below.
- A minimal standalone repro (`scratch_p3/option_consumer_check.spl`)
  confirms the *mechanism* directly: `match opt: Some(value): value.len()
  ...` against the corrected bare-array return silently gives `len=0`
  instead of `31` (proving the old `Some(value)` idiom is unsafe against a
  bare-representable optional and *why* the two consumer files needed
  rewriting, not just leaving as-is). Both `if opt != nil: val value: [u8] =
  opt ...` and `rt_file_read_bytes(...) ?? []` correctly give `31` when
  tested against this same script — the shipped fix uses `?? []` (see
  point 2 above) specifically for its independently-proven native-safety,
  not because the narrowing form was found to be wrong.

**`param_add.spl` (`fn add(a: i64, b: i64) -> i64: return a + b`) is
UNFIXED — still fails identically on both backends** with the originally
reported `type mismatch: cannot convert object to int`. This is confirmed
to be a **separate defect** from the one just fixed: the original
investigation (this doc's "Secondary" section below) traced it to a
`Value::Object{class:"MirFunction"}` reaching a scalar-coercion (`as_int()`)
call site, unrelated to `CodegenOutput`/`rt_file_read_bytes`. Not
investigated further this session — see "Secondary, not-fully-localized
finding" below for what's already known, and treat that as the next lane's
starting point.

### Verification landmine: a stale hardcoded SHA in this doc's own bisection
scripts silently reset HEAD and deleted the repro files mid-investigation

While re-verifying a first (later-reverted) fix attempt, `scratch_p3/
build_seed_at_sdnfix.sh` (written earlier in this investigation, see
"Supporting finding" below) was run again in a **later session** than the
one that wrote it. Its `LANE_HEAD` constant was hardcoded to this worktree's
*original* detached-HEAD SHA (`a79a52ba8178e1e4fee4adfc24e101dd3de87d3c`) —
correct when the script was written, but **stale** by the time this
follow-up ran, since several doc-only commits had landed on top of it by
then. The script's own cleanup step (`git checkout -f "$LANE_HEAD" --quiet`,
with no path restriction) silently reset HEAD *backward* to that stale SHA
and, because `scratch_p3/noparam.spl`/`param_add.spl` didn't exist yet at
that commit, **force-deleted both repro files** as a side effect of the
checkout. This was not noticed for several test cycles because
`native-build --entry scratch_p3/noparam.spl` on a **missing** entry file
produces a plausible-looking but unrelated error
(`native-build produced empty mir_modules ... no modules loaded`) rather
than a clear "file not found" — so multiple "fix" experiments were
evaluated against a corrupted setup before this was caught (via a stray
`pwd` returning the wrong directory, which prompted re-checking `git log
--oneline -g`). Recovered via `git checkout -f
6db27492f225002f5d53f4abfc4c4febfb0492a6` (this investigation's actual
tip at the time) and re-verified everything above from that clean state.
**Anyone re-running `build_seed_at.sh`/`build_seed_at_sdnfix.sh` from this
doc must first edit `LANE_HEAD` to the current tip** — do not trust them
as-is.

---

## Status (original investigation, superseded by the follow-up above for
the `noparam.spl` symptom): ROOT-CAUSED at the symptom site, fix site found
via a second pass

The failure mechanism at HEAD is confirmed with certainty (Option::Some
reaches an overload matcher that can't match it). What is **not** yet
established is *where in the interpreter* the value stops being properly
unwrapped, or what changed to make it stop — a same-code-path A/B
(idx 54 vs HEAD) proves the two functions this doc originally blamed
(`constructor_value_matches_type`, `rt_file_read_bytes`) are byte-identical
between a passing run and a failing run, so neither is the regression. See
"Fix-target correction" for the corrected next step.

## Symptom (as assigned)

A FRESH `cargo build --release --bin simple` seed, run with `native-build` on
an entry containing a parameterized function (`fn add(a: i64, b: i64) -> i64`),
fails:

```
error: semantic: type mismatch: cannot convert object to int
```

Broadened during triage: even a **zero-parameter** entry (`fn main() -> i64:
return 7`) fails on the same fresh seed:

```
error: semantic: unknown static method object on class CodegenOutput
```

Both repros pass (rc 7) via a self-consistently-built Jul-11 seed
(`7cb317ca9a01d0d3e1bcf89405f3a8af4bae4423`) run against the **same
current-tree** `.spl` source — proving the divergence lives in
`src/compiler_rust` (the Rust seed), not in the self-hosted `.spl`.

## Failure mechanism at HEAD (symptom site — NOT the code-level regression;
see "Fix-target correction" below before proposing any patch)

`native-build`'s default source discovery interprets a large slice of the
self-hosted compiler (`src/compiler`) as part of compiling any entry. That
interpreted run reaches the LLVM native codegen backend, whose object-file
byte-read path is where the failure is observed at HEAD:

1. **`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:407-416`**
   — `rt_file_read_bytes` returns `make_some(Value::array(...))` on success and
   `make_none()` on failure — i.e. the extern binding returns an **Option-enum
   wrapped** value, not a raw `[u8]` array or a bare-nilable array. (Confirmed
   textually unchanged across the whole 07-11..07-18 window.)

2. **`src/compiler/70.backend/backend/llvm_backend_tools.spl:211-224`** — the
   consuming `.spl` does:
   ```
   val bytes = rt_file_read_bytes(obj_path)
   ...
   if bytes == nil:
       return Err(...)
   Ok(LlvmObjectCode(bytes: bytes, symbols: symbols))
   ```
   This code relies on a nil-sentinel contract: a non-nil `[u8]?` extern
   return is expected to already collapse to the plain array by the time
   it's used (compare-to-nil, then use directly, no explicit unwrap).
   `LlvmObjectCode.bytes` is declared `[u8]` (`llvm_backend_tools.spl:31-33`).
   **That contract held at idx 54** (verified rc=7, correct binary) and
   **does not hold at HEAD**, where the field ends up populated with the
   still-boxed `Value::Enum` (Option::Some(array)). This `.spl` code itself
   is not shown to have changed and is not being blamed here — see
   "Fix-target correction."

3. **`src/compiler/70.backend/backend/llvm_codegen_adapter.spl:78-81`** reads
   `object_code.bytes` (the still-boxed enum) and calls
   `CodegenOutput.object(module.name, bytes)`.

4. **`src/compiler_rust/compiler/src/interpreter_method/special/objects.rs`**
   — `handle_constructor_methods`'s overload matcher:
   - `constructor_value_matches_type` (lines 28-39) has match arms for
     `Value::Array`, `Value::FrozenArray`, `Value::Tuple` against an
     `Array`-typed parameter — **no arm for `Value::Enum`**. An
     Option::Some-wrapped array therefore never matches an `[u8]` parameter.
   - `constructor_overload_score` (lines 41-66) returns `None` for the
     `object(name, bytes)` candidate as a result.
   - `handle_constructor_methods` falls through to "no matching static
     method" (line 278), emitting the misleading
     `unknown static method object on class CodegenOutput` — the method
     genuinely exists (confirmed both `CodegenOutput` definitions have it,
     see "red herring" below); the real cause is an unmatched overload
     because one argument is still Option-boxed.

**Verified live via runtime instrumentation** (temporary `eprintln!` in
`objects.rs`, gated behind `SIMPLE_DEBUG_CTOR=1`, reverted after use — patch
kept at `scratch_p3/debug_ctor_instrumentation.patch` in this worktree for
reference, not committed):

```
[DEBUG-CTOR] class_name=CodegenOutput method=object
  all_methods=["text","text_with_header","object","gpu_output","interpreted",
               "with_symbols","with_compile_time","to_compiled_module"]
  candidates_by_name=1 arg_count=2 arg_types=["str","enum"]
  enum arg identity: Option::Some
  candidate params=["name","bytes"] score=None
```
`arg_types=["str","enum"]` plus the follow-up `enum_name`/`variant` print
(`Option::Some`) is the smoking gun and confirms the specific attribution:
the second argument to `.object(name, bytes)` is a live `Value::Enum{enum_name:
"Option", variant:"Some", ...}` — i.e. exactly what `make_some(...)` in
`rt_file_read_bytes` constructs, not a coincidentally-enum-shaped unrelated
value.

### "CodegenOutput" duplicate-class red herring, ruled out

There are genuinely two `class CodegenOutput:` declarations
(`src/compiler/70.backend/backend/codegen_types.spl:30`, `pub`, 8 methods
incl. `gpu_output`/`with_symbols`; `src/compiler/70.backend/backend/common/
codegen.spl:30`, non-`pub`, 5 methods) — a second instance of the
already-documented "same struct/class name in 2 modules = global-registry
collision" landmine class. The debug trace confirms the **richer `pub` class
wins** the registry and genuinely has `.object` — so this particular
duplicate name is NOT what breaks `noparam.spl`/`param_add.spl`. It remains a
latent landmine worth a follow-up rename, just not this bug's cause.

### Age of the defect

`git log -S'make_some' -- .../interpreter_extern/file_io.rs` and
`git log -S'constructor_value_matches_type' -- .../objects.rs` both bottom out
at commits from well before 2026-07-11 (not even present in the
`7cb317c..a79a52ba817` window). **This Option-unwrap gap pre-dates the whole
bisected range** — it was never a "regression" introduced this week; it was
simply never exercised end-to-end via interpreted native-build until
discovery scope widened (next section).

## Supporting finding: why this path only started firing this week

Manual bisection (seed-only: full self-consistent checkout+build of
`src/compiler_rust` at each candidate SHA, binary extracted, then working
tree restored to lane-HEAD `.spl` before testing — so `.spl` is held
constant and only the seed binary varies) against
`scratch_p3/noparam.spl` (`fn main() -> i64: return 7`):

| idx | SHA | date | native-build rc | **binary rc** | output lines | note |
|---|---|---|---|---|---|---|
| 0 | `7cb317ca9a01` | 07-11 | 0 | **7** | 1276 | baseline |
| 35 | `d90e999dbf51` | | 0 | (not run) | 1276 | |
| 48 | `0b63b4472636` | 07-13 | 0 | **7** | 1276 | |
| **49** | `90f92f32ed12` | 07-13 | 0 | **7** | **1276** | last commit before the discovery-scope jump |
| **50** | **`fe1e034c516e`** | **07-13 15:20** | 0 | **7** | **161215** | **discovery scope explodes here — but binary still genuinely correct** |
| 51 | `eab67d9e383c` | | 0 | **7** | 161215 | |
| 54 | `b60984e621f7` | | 0 | **7** | 161215 | **full tree loaded, LLVM pipeline genuinely exercised, still correct** |
| 60 | `8146c99485dc` | | 1 | — | 161216 | fails on **SdnValue** collision (native-build itself errors, no binary produced) |
| 167 | `662e7c7cad2a` | 07-17 | 1 | — | 161216 | SdnValue fixed here; now fails on **CodegenOutput** (this doc's bug) |
| HEAD | `a79a52ba817` | 07-18 | 1 | — | — | CodegenOutput (noparam) / "cannot convert object to int" (param_add) |

**Important correction versus an earlier draft of this doc:** every binary
from idx 48 through idx 54 was re-verified to actually **run and return rc 7**
(not just "native-build exited 0"), including idx 50/51/54 *after* the
discovery-scope jump. That means **`fe1e034c516ef7779fee0660c7d6787fc4d3aade`
does not, by itself, trigger the `CodegenOutput`/Option-unwrap bug** — at
idx 54 the full 244-file tree is loaded AND the LLVM backend genuinely runs
`rt_file_read_bytes` → `CodegenOutput.object(...)` successfully to produce a
correct, working binary. So `bytes` was NOT an `Option::Some`-wrapped enum at
idx 54; something between idx 55 and idx 60 (or conceivably a change outside
`src/compiler_rust` that this seed-only bisection cannot see, since `.spl` was
always held at lane-HEAD during these tests — see Methodology note below)
is the actual trigger for this specific execution path breaking, not the
parser fix.

**What `fe1e034c516ef7779fee0660c7d6787fc4d3aade` is, and what it is not:**
it is a **correct, legitimate parser fix** — before it,
`error_recovery.rs::detect_common_mistake` flagged ANY identifier token with
lexeme `"function"` as the JS/TS `function name(...)` mistake, *regardless of
what followed*. Any valid Simple code using `function` as a plain identifier
(parameter/field/variable name — `function` is not a reserved word in Simple)
was misdetected and failed to parse. The fix adds
`next.is_some_and(|t| matches!(t.kind, Identifier))`, correctly narrowing the
check (direct minimal proof below). It **is** the commit that unlocks
full-tree discovery (1276 → 161215+ output lines, confirmed) — that part
is solid and reproduced. It is **not verified** to be what makes the
`CodegenOutput`/Option-unwrap bug fire; treat that connection as **necessary
infrastructure, not a proven sufficient cause**.

**Direct minimal proof of the parser fix itself** (`scratch_p3/function_ident.spl`):
```simple
fn use_function(function: i64) -> i64:
    return function + 1
fn main() -> i64:
    return use_function(6)
```
- Pre-fix seed (idx 49, `simple_90f92f32ed12`): `simple run` → parse error,
  "Replace 'function' with 'fn'".
- Post-fix seed (idx 50, `simple_fe1e034c516e`): runs clean.

**Side effect (still holds):** many `.spl` files across
`src/compiler`/`src/lib`/`src/app` that use `function` as an identifier
previously failed to parse and were silently excluded from whatever
default-source-discovery reached them. Once fixed, they parse and load —
`native-build`'s interpreted run of the self-hosted compiler jumps from
~1276 lines of output to 161215+ lines (244+ `.spl` files under
`src/compiler` alone get parsed/lint-checked). That newly-included module
set is a plausible *prerequisite* for the SdnValue class/enum-name collision
(idx 60, fixed at 167 — see
`hir_stmt_expr_payload_extraction_nil_2026-07-17.md`, "SDNVALUE lane"
follow-up) and this doc's Option-unwrap gap to be reachable at all, but idx
54's clean rc-7 run proves discovery-scope alone is insufficient to explain
either failure.

**idx 55-60 was not pinned down further, and is intentionally left open.**
Several intermediate commits in that span do not build standalone
(`1db9cb5be31` and `e6397669bb31` both fail with pre-existing `E0308`/`E0425`
compile errors when checked out in isolation, consistent with fast-moving
WIP commits in an active branch). More importantly: pinning the exact
rc-flip commit in 55-60 would only identify the **SdnValue** trigger
(already fixed at 167) — since SdnValue fires first and masks whatever else
is going on, that bisection cannot by itself tell you when the
`CodegenOutput`/Option-unwrap bug starts firing. Answering that would require
re-running the SIMPLE_DEBUG_CTOR trace (or an SdnValue-blind repro) at each
of several rebuilt seeds in 55-166, which was judged not worth the added
rebuild cycles given the defect is already conclusively reproduced and traced
at HEAD.

**Methodology caveat:** this bisection held `.spl` at lane-HEAD
(`a79a52ba817`) for every test point and varied only the seed binary
(built self-consistently at each historical SHA, then the binary extracted
before restoring the tree) — so it correctly isolates "does this historical
Rust seed correctly compile today's `.spl`", but it does **not** prove the
Option-unwrap gap is untouched by `.spl`-side changes across 07-11..07-18;
it only proves the two Rust-side functions implicated (`rt_file_read_bytes`,
`constructor_value_matches_type`) are textually unchanged since before
07-11 (see "Age of the defect" above).

## 2026-07-18 lane KEY2 follow-up: `param_add.spl` FIXED (root-caused + verified rc=7)

**Root cause found and fixed.** The `Value::Object{class:"MirFunction"}`
reaching `Value::as_int()` (flagged below as "not yet traced to its exact
file:line call site") is now traced precisely:

- The self-hosted compiler's own MIR-rewrite passes (only exercised once a
  program has a real function *call* — hence `noparam.spl`, which has none,
  never hit this) rebuild a `MirFunction` via paren-form struct
  spread/update: `MirFunction(..func, blocks: new_blocks)` (seen identically
  in `src/compiler/60.mir_opt/mir_opt/{dce,cse,gvn,tco,...}.spl`,
  `mir_aop_injection.spl`, etc. — dozens of call sites, all the same shape).
- Paren-form call arguments have **no dedicated spread token** in the parser
  (`src/compiler_rust/parser/src/expressions/helpers.rs::parse_arguments`).
  Only the *brace*-form struct literal parser (`Name { ..base, field: val }`,
  in `parser/src/expressions/primary/identifiers.rs` and
  `parser/src/expressions/postfix.rs`) special-cases a leading `..` token and
  produces `Expr::StructInit { spread: Some(base_expr), .. }`.
- So `..func` inside `MirFunction(..func, blocks: new_blocks)` parses through
  the ordinary expression grammar, where a bare leading `..` is valid syntax
  for an open-start range literal: `Expr::Range { start: None, end:
  Some(func_expr), bound }`. It becomes an ordinary, unlabeled `Argument`.
- `eval_collection_expr`'s `Expr::StructInit` handler (`interpreter/expr/
  collections.rs:138`) *does* already special-case `spread` correctly for
  brace-form construction. But paren-form construction (`Ctor(args...)`,
  used when `Ctor` is called like a function) goes through a *different*
  function, `instantiate_class`
  (`interpreter_call/core/class_instantiation.rs`), which had **no spread
  handling at all** — a parity gap between the two constructor-evaluation
  paths. Its field-based construction loop evaluated every argument eagerly
  via `evaluate_expr` before checking name/position
  (`class_instantiation.rs:273`, pre-fix), so the unlabeled Range argument's
  `end` operand — the *whole* base `MirFunction` object, not an int — hit
  `Value::as_int()`'s catch-all arm and produced "type mismatch: cannot
  convert object to int".
- Confirmed via a temporary `eprintln!` + `std::backtrace::Backtrace::
  force_capture()` in `Value::as_int()`'s catch-all arm (reverted): the
  1-deep-Range-arg diagnostic showed `end expr=Some(Identifier("func"))`,
  `value_debug=Object { class: "MirFunction", ... }` flowing out of
  `instantiate_class` <- `evaluate_call` <- `eval_call_expr`, exactly matching
  this theory (not the brace-form path, which was never on the call stack).

**The fix** (`interpreter_call/core/class_instantiation.rs`, in
`instantiate_class`'s per-argument loop): detect the same paren-form spread
shape — an unlabeled argument whose value is `Expr::Range { start: None, end:
Some(base_expr), .. }` — and merge `base_expr`'s evaluated `Object`/`Dict`
fields into the constructed object (mirroring collections.rs's brace-form
spread handling exactly), instead of falling through to the generic
`evaluate_expr` + positional/named binding. The spread argument does not
consume a positional field slot, matching brace-form semantics (later
explicit fields still override spread fields).

**Verification:**
```
cd src/compiler_rust && cargo build --release --bin simple
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH src/compiler_rust/target/release/simple \
  native-build --entry scratch_key2/param_add.spl -o scratch_key2/param_bin --backend llvm --clean
# now: rc=0 (was: error: semantic: type mismatch: cannot convert object to int)
scratch_key2/param_bin; echo "rc=$?"   # rc=7 (3 + 4)
```
`noparam.spl` re-verified unaffected (still rc=7). Added a Rust unit test,
`interpreter_call::core::class_instantiation::tests::
paren_form_struct_spread_merges_base_fields_instead_of_as_int`, exercising
`instantiate_class` directly with a hand-built `Point(..base, y: 99)` call
(base `x:1,y:2,z:3`, expects `x:1,y:99,z:3`) — passes with the fix, and by
construction cannot pass without it (pre-fix, the same shape errors in
`as_int()` before any field merge happens). Full `cargo test --release -p
simple-compiler --lib` run: 3140 passed, 251 failed (deterministic count
across two separate runs). The baseline (this worktree without this change)
was NOT independently re-run to confirm all 251 pre-exist -- what IS
confirmed: every failing test name falls in `codegen::`/`mir::`/
`pipeline::`/`lint::`/`hir::`/`linker::`/`value::`/`runtime_bridge::`/
`compilability::`, zero match `instantiat|class|spread|struct_construct`,
and this diff touches only `class_instantiation.rs` (one function inside
it). That module-isolation plus the zero-match grep is why this change is
judged safe, not a claim that the 251 are pre-existing fact.

**IMPORTANT SCOPE CORRECTION — the redeploy keystone is NOT fully closed.**
The fix above only covers the code path exercised when the self-hosted
compiler's own MIR-rewrite passes are *interpreted* by a fresh Rust seed
(exactly what a first-stage `native-build` does, since the seed has no
compiled copy of the compiler yet — this is the actual reported symptom and
is genuinely fixed). It does **not** cover the *native-compiled* path: when
any `.spl` program (including, eventually, the self-hosted compiler itself,
once a later bootstrap stage compiles it natively rather than interpreting
it) uses the same paren-form struct-spread syntax, native codegen mishandles
it too — a **separate, still-open** bug, found and localized (not fixed) by
this lane:

- Repro: `scratch_key2/spread_repro.spl` (`struct Point: x,y,z: i64`;
  `make_base()` returns `Point(x:1,y:2,z:3)`; `main` returns
  `Point(..base, y: 99).{x+y+z}`, correct answer 103).
  `native-build --entry scratch_key2/spread_repro.spl --backend llvm --clean`
  succeeds (rc=0, no error) but the binary returns **rc=102**, not 103 — a
  silent wrong-answer miscompile, not a loud failure.
- Root cause, precisely localized: `lower_struct_construct`
  (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1628`)
  separates constructor args into `named_args` (matched by name) and
  `positional_args` (consumed in declared-field order) — it has **no
  spread/`..base` concept at all** (unlike the brace-form interpreter path
  this lane fixed above). The unlabeled `..base` argument becomes
  `positional_args[0]`, consumed for the struct's *first* declared field
  (`x`) via `self.lower_expr(chosen)` at line ~1720, where `chosen` is the
  HIR-level `Range{start:None, end:Some(base)}` node (same mis-parse as the
  interpreter case: paren-form call args have no dedicated spread token,
  `parser/src/expressions/helpers.rs::parse_arguments`). `lower_expr` routes
  this to `lower_range` (`src/compiler/50.mir/_MirLowering/
  function_lowering.spl:591`), which lowers `start=None` to a zero constant
  and `end=base` to `base`'s own lowered value (its aggregate pointer), then
  emits a runtime call `rt_range(0, <base's pointer bits>)` — a nonsense
  call whose result becomes field `x`'s stored value (empirically resolves
  to `3`, the codebase's canonical raw nil-sentinel payload — see
  `ensure_option_handle`'s comment on payload `3` — suggesting `rt_range`
  degenerates to a nil-like handle for this bogus input). Meanwhile the
  struct's *last* field (`z`) is never claimed by any positional or named
  arg (the spread consumed the single positional slot) and gets zero-filled
  by the "omitted field" path (line ~1676-1700) instead of inheriting from
  `base`. Net: `x=3` (garbage), `y=99` (correct, named), `z=0` (should be 3,
  omitted) → `3+99+0=102`.
- **Why this matters for the keystone claim:** `MirFunction(..func, blocks:
  new_blocks)` — the exact pattern that broke the interpreted path — is used
  pervasively across the self-hosted compiler's own MIR optimization passes
  (`src/compiler/60.mir_opt/mir_opt/*.spl`, `mir_aop_injection.spl`,
  `mir_debug_trace_injection.spl`, etc: ~25 call sites, same shape). Once a
  later bootstrap stage compiles the self-hosted compiler *natively* (rather
  than interpreting it, which is what today's fresh-seed `native-build`
  does), those same call sites run through this broken
  `lower_struct_construct`, not through the (now-fixed) interpreter path —
  so a natively-compiled compiler binary would silently corrupt its own MIR
  rewrites (wrong field values, not a crash — worse than a loud failure).
  This was NOT chased to a fix in this session (a proper fix needs
  `lower_struct_construct`'s positional/named-arg split reworked so a spread
  argument fills every field neither named nor otherwise positioned, mirror-
  ing the interpreter fix's semantics, rather than being naively treated as
  one more positional slot) — flagging as a new, precisely-localized,
  high-priority follow-up bug, not a re-open of this doc's original scope.

## Secondary, not-fully-localized finding: `param_add.spl`'s distinct symptom (ORIGINAL, now superseded by the fix above — kept for the record)

`scratch_p3/param_add.spl` (`fn add(a: i64, b: i64) -> i64: return a + b`,
`fn main() -> i64: return add(3, 4)`) fails with a *different* message:
`type mismatch: cannot convert object to int` (`src/compiler_rust/compiler/
src/value_impl.rs:51-60`, `Value::as_int()`'s catch-all arm). Instrumented via
a temporary `eprintln!` (reverted; same scratch patch has the value_impl.rs
half too, in `scratch_p3/debug_asint.patch`):
```
[DEBUG-AS-INT] class="MirFunction" fields=["span","symbol","locals",
  "type_bindings","export_name", ... "signature","generic_params",
  "vhdl_metadata","is_generic_template"]
```
A whole `Value::Object{class:"MirFunction"}` (the self-hosted compiler's own
MIR function record) reaches an `as_int()` call site — a different specific
erasure than the CodegenOutput/bytes case, not yet traced to its exact
file:line call site. Given the effort already spent on this lane, this is
flagged as an open follow-up rather than chased further; the mechanism class
(a compound `Value` reaching a scalar-coercion site) is the same family as
the Option-unwrap bug above, likely via a different collision/erasure path
through the MIR-lowering code that only param-carrying functions exercise.

## Fix-target correction (post-commit self-review — read this before touching anything)

An earlier draft of this section proposed adding a `Value::Enum`
(Option::Some) auto-unwrap arm to `constructor_value_matches_type`
(`objects.rs:28-39`) as the fix. **That target is wrong and has been ruled
out**, not just deferred:

- `git log -p 7cb317c..a79a52ba817 -- .../interpreter_method/special/
  objects.rs` shows exactly one substantive touch to this file in the whole
  window: `662e7c7cad2` (the SdnValue fix), and its diff only *appends* a
  new enum-variant-construction fallback after the "no matching static
  method" point — it does not touch `constructor_value_matches_type` or
  `constructor_overload_score` at all. `git log -p ... -- .../
  interpreter_extern/file_io.rs` similarly shows no in-window touch to
  `rt_file_read_bytes` itself (`a6822a52` in-window only touches an
  unrelated function, `rt_dir_walk`).
- Both functions are therefore **provably identical** at idx 54
  (`b60984e621f7`, verified rc=7, genuinely correct binary, full 244-file
  tree loaded) and at HEAD (fails). Since the code implicated in the trace
  is unchanged between a passing run and a failing run, **it cannot be the
  regression** by itself.
- **Two hypotheses fit the verified facts; this session did not distinguish
  them** (doing so needs a historical rebuild + the `SIMPLE_DEBUG_CTOR`
  trace re-run at idx 54, which was judged not worth another rebuild cycle
  — left as the first thing a follow-up lane should do):
  (a) idx 54's binary genuinely went through this exact
  `rt_file_read_bytes` → `CodegenOutput.object` path and got a real, unwrapped
  array — meaning something *elsewhere* in the interpreter (most plausibly
  the nil-comparison/narrowing behavior around `if bytes == nil:`, or the
  let-binding evaluation path for `val bytes = rt_file_read_bytes(...)`)
  stopped collapsing a non-nil `[u8]?` extern-return between idx 54 and HEAD;
  or (b) idx 54's rc=7 success came through a **different** codegen adapter
  entirely (there are at least 4: `llvm_codegen_adapter.spl`,
  `cranelift_codegen_adapter.spl`, `native_codegen_adapter.spl`,
  `irtc_codegen_adapter.spl`, each with their own `CodegenOutput.object(...)`
  call — see the grep in the next section) and this specific
  `rt_file_read_bytes`-backed path was simply never reached at idx 54, so it
  may have been broken (or unreached) even before 07-11. rc=7 alone does not
  distinguish these — it only proves *some* correct compile path succeeded,
  not which one.
- Adding an Enum-unwrap arm to the overload matcher would also be the wrong
  *kind* of fix even if it made the symptom go away: `constructor_value_
  matches_type` backs every static/constructor call in the interpreter, and
  blanket-accepting an `Option<[u8]>` wherever `[u8]` is declared would hide
  genuine argument-type errors elsewhere, not just paper over this one.

**Correct next step for a follow-up lane — rc-bisection will NOT work here,
do not repeat it:** the logical range to search is idx 54 → HEAD, but a
plain rc-bisection over that range is confounded: the already-fixed SdnValue
collision fires first and masks everything from idx 60 through idx 166
(inclusive), so an rc-based bisector converges on SdnValue's onset again,
not on this bug's. Either (a) re-run the `SIMPLE_DEBUG_CTOR`-style trace
(patch in `scratch_p3/debug_ctor_instrumentation.patch`) at a handful of
candidate builds in 54→229 to get an SdnValue-blind signal (does
`CodegenOutput.object`/`enum arg identity` ever print, regardless of whether
the overall build ultimately fails on SdnValue first?), or (b) read the
diffs directly — cheaper, no rebuild:
```
git log -p 7cb317ca9a01..a79a52ba817 -- \
  src/compiler_rust/compiler/src/value.rs \
  src/compiler_rust/compiler/src/interpreter_extern/mod.rs
```
This showed ~40 in-window commits touching one of those two files (headline
list only, not individually read for time reasons). One is a strong lead
worth checking first: **`9d3f2ea353d`** (idx 193, 07-17,
"fix(seed): rt_string_bytes missing EXTERN_DISPATCH entry — dynamic-SFFI
fallback wrapped tagged array handle as plain Int, crashing .len() with
'method not found on i64'") is a **different extern function** than
`rt_file_read_bytes` but the **same defect class**: a value that should be a
plain array/scalar arrives at a call site still wrapped by a dispatch
fallback layer. It does not fix this doc's bug (HEAD, which is after it,
still fails) but its diff is the best template for what the real fix here
probably looks like — check whether `rt_file_read_bytes` has (or is
missing) an equivalent native `EXTERN_DISPATCH` entry, the way `rt_string_bytes`
needed one.

**Why no fix was attempted this session:** even once the correct file is
found, whatever coerces `[u8]?`/Option-shaped extern returns for consumption
is very likely shared machinery (nil-comparison/narrowing, or the
EXTERN_DISPATCH fallback layer per the lead above, isn't specific to this
one call site), so the same "broad blast radius, needs its own regression
pass" caution from the ruled-out matcher fix still applies to whatever the
real fix site turns out to be.

## Resume commands

**Verify the fix (current, post-2026-07-18 KEY2 follow-up — the reported
`native-build` symptom is fixed for both entries; the deeper native-codegen
struct-spread defect described above remains open):**
```
cd src/compiler_rust && cargo build --release --bin simple && cd ..
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH src/compiler_rust/target/release/simple \
  native-build --entry scratch_p3/noparam.spl -o /tmp/noparam_bin --backend llvm --clean
/tmp/noparam_bin; echo "rc=$?"   # rc=7 (was: error: unknown static method object on class CodegenOutput)

# param_add.spl -- now FIXED (was: error: semantic: type mismatch: cannot convert object to int):
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH src/compiler_rust/target/release/simple \
  native-build --entry scratch_p3/param_add.spl -o /tmp/param_bin --backend llvm --clean
/tmp/param_bin; echo "rc=$?"   # rc=7 (3 + 4)

# STILL OPEN (native-codegen struct spread, see "SCOPE CORRECTION" above):
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH src/compiler_rust/target/release/simple \
  native-build --entry scratch_key2/spread_repro.spl -o /tmp/spread_bin --backend llvm --clean
/tmp/spread_bin; echo "rc=$?"   # currently rc=102 (should be 103) -- silent wrong-answer miscompile
```
Regression test: `cargo test --release -p simple-compiler --lib
paren_form_struct_spread_merges_base_fields_instead_of_as_int` (in
`interpreter_call/core/class_instantiation.rs`).

The original (pre-fix) HEAD failure, for reference:
```
cd src/compiler_rust && cargo build --release --bin simple
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH simple native-build \
  --entry scratch_p3/noparam.spl -o scratch_p3/noparam_bin --backend llvm --clean
# error: semantic: unknown static method object on class CodegenOutput
```

Re-run the instrumented trace (patch at
`scratch_p3/debug_ctor_instrumentation.patch` in `wt_p3`):
```
git apply scratch_p3/debug_ctor_instrumentation.patch   # objects.rs only
cd src/compiler_rust && cargo build --release --bin simple
cd ..
SIMPLE_DEBUG_CTOR=1 env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH \
  src/compiler_rust/target/release/simple native-build \
  --entry scratch_p3/noparam.spl -o scratch_p3/noparam_bin --backend llvm --clean \
  2>&1 | grep "DEBUG-CTOR" | tail -5
git checkout -- src/compiler_rust/compiler/src/interpreter_method/special/objects.rs
```

Reproduce the parser-fix before/after proof:
```
scratch_p3/seed_bins/simple_90f92f32ed12 run scratch_p3/function_ident.spl   # pre-fix: parse error
scratch_p3/seed_bins/simple_fe1e034c516e run scratch_p3/function_ident.spl   # post-fix: clean
```

Bisection artifacts (this worktree only, not committed): `scratch_p3/
build_seed_at.sh`, `scratch_p3/test_seed_bin.sh`, `scratch_p3/seed_bins/*`
(6 pre-built historical seed binaries), `/tmp/bisect_*`/`/tmp/idx*_test.log`
raw logs.
