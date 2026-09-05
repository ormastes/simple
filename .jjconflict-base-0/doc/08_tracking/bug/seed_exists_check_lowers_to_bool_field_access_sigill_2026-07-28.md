# Rust seed lowers `.?` to a bare bool — value-position `x.?.field` SIGILLs

- **Date:** 2026-07-28
- **Status:** FIXED 2026-07-28 in the Rust seed's HIR lowering (see "Fix" at the bottom)
- **Severity:** blocker — sole remaining blocker on the `web x headless` showcase cell
- **Lane:** `bin/simple run` (which is the **Rust bootstrap seed**, see "Which binary" below)
- **Not** the `class X with Trait` duck-dispatch `ud2` (that theory is REFUTED below)

## Symptom

`compute_styles(..., vector_fonts: true)` on the canonical web showcase document
aborts with `runtime error: field access on nil receiver` followed by SIGILL
(exit 132, core dumped). Reproducible 100% of runs, in seconds.

## Reproduction (13 lines, ~3 s, no showcase harness needed)

```
class C:
    a: text
    b: text

fn f1() -> C?:
    C(a: "p", b: "P1")

fn main() -> i64:
    val r1 = f1()
    print "[m] nil={r1 == nil}"      # false   (correct)
    val u = r1.?
    print "[m] u={u}"                # true    (WRONG - should be the C value)
    print "[m] b={u.b}"              # SIGILL: field access on nil receiver
    0
```

Run: `bin/simple run <file>.spl` -> exit 132.

Control that PASSES in the same file: `if val u1 = r1:` binds the real object and
`u1.b` prints `P1`. Only the value-position `.?` is broken.

## Proven fault site (disassembly at the faulting address)

`gdb -batch -ex run -ex "x/6i $rip-8" --args bin/simple run min3.spl`:

```
   0x573265c25d5: mov    -0x23d3(%rip),%edx     # rt_eprintln_str
   0x573265c25db: call   *%rdx                  # prints the diagnostic
=> 0x573265c25dd: ud2                           # <-- SIGILL, bytes 0f 0b
   0x573265c25df: and    $0xfffffffffffffff8,%r9   # ok_block: obj &= ~0x7
   0x573265c25e3: mov    0x8(%r9),%rsi             # field load at offset 8
```

Instruction bytes at `$rip`: `0f 0b 49 83 e1 f8 49 8b` — `0f 0b` is `ud2`.

That is exactly the error block of `guard_nonnull_receiver` in
`src/compiler_rust/compiler/src/codegen/instr/fields.rs:38`
(`builder.ins().trap(TrapCode::unwrap_user(12))`). It is a deliberate
nil-receiver diagnostic trap, NOT a duck-dispatch stub and NOT a wild jump.

Note the call form: `mov <disp>(%rip),%edx ; call *%rdx`. Grepping a disassembly
for `call <symbol>` finds nothing here — read around the address instead.

## Root cause

`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:985` `lower_exists_check`
lowers `Expr::ExistsCheck` (the `.?` operator) to:

```
BuiltinCall { name: "rt_is_some", args: [inner] },  ty: TypeId::BOOL
```

So `x.?` evaluates to the boolean `true` (integer 1). A following field access
masks the receiver with `~0x7` (`1 & ~7 == 0`), hits the null-receiver guard, and
executes `ud2`.

This contradicts the language spec. `doc/07_guide/quick_reference/syntax_quick_reference.md:497`
"Existence Check (`.?`) — Returns `T?`": *"It returns `T?` — the value itself if
present, `nil` if absent."*

Both other engines already agree with the spec:

- Interpreter: `src/compiler_rust/compiler/src/interpreter/expr.rs:503` returns
  the value (or `Value::Nil`), never a bool.
- Pure-Simple compiler: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2400`
  emits a real branch and its comment names this exact defect —
  *"It must NOT collapse to the bare `rt_is_some` bool: that discarded the payload
  ... the native-smoke-matrix '(14) Option/nil check (x.?)' regression."*

**The fix was made in the Simple compiler and never ported to the Rust seed.**

## Which binary — why this reaches a production lane

`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` (145 MB, built
2026-07-27) prints on startup:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as
the normal tool. Build and use the pure-Simple bin/simple instead.
```

So the whole showcase lane currently runs on the seed, which carries the
un-ported defect. `src/compiler_rust/target/release/simple` (57 MB, 2026-07-28
01:03) reproduces identically.

## Path from the minimal repro to the showcase SIGILL

Bisected top-down, each step confirmed by running it in isolation:

1. `compute_styles(nodes, rules, child_index, false, true)` — faults between
   trace stages `metric-language-ready` and `metrics-ready`, node index 5
   (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:1902-1909`).
2. `resolve_font_metrics_with_language("sans-serif", "<20 chars>", 16, "en")`
   alone SIGILLs (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:2097`).
3. `selected_font_asset_for_language_category("en", "sans")` alone SIGILLs
   (`src/lib/common/encoding/font_registry.spl:758`).
4. Inside it: `val resolved = cell.?` then `resolved.status` — `cell.?` is `true`,
   `.status` traps. `selected_font_coverage_cell` itself returns correctly and the
   coverage matrix walks cleanly (all 100 cells printed), so the data is fine.

Downstream sites on the same path that would fault next:
`font_renderer.spl:2015` `selected_candidate.?.family`, `:2017`
`selected_font_asset_identity(selected_candidate.?)`, `:2027`
`_resolve_selected_shaped_glyph_run(selected_candidate.?, ...)`.

## Why the showcase only started SIGILLing now

An uncommitted working-copy edit to
`src/lib/nogc_sync_mut/text_layout/font_provider.spl` replaces the
`std.nogc_sync_mut.sffi.system` import with a local `extern fn
rt_process_run_timeout`, to keep `rt_sleep_ms` (unresolved in the JIT symbol
table) out of the module graph. A/B proven:

| `font_provider.spl` | result |
|---|---|
| `origin/main` version | `[INFO] JIT compilation failed ... unresolved external symbol 'rt_sleep_ms'` -> whole module runs INTERPRETED -> correct `.?`, no SIGILL, ~285x slower |
| working-copy version | module JIT-compiles -> `.?` miscompiles -> SIGILL |

So the JIT unblock did not introduce the defect; it stopped masking it. Both
states are broken: one is slow-and-correct, the other is fast-and-crashing.

## Refuted hypotheses

- **`class X with Trait` mixin duck-dispatch `ud2`** — REFUTED. The trapping
  `ud2` is the nil-receiver guard in `instr/fields.rs`, immediately preceded by a
  `call *%rdx` to `rt_eprintln_str` printing the nil-receiver message. A
  duck-dispatch stub has no such preceding diagnostic call.
- **Jump into data / nil function pointer** — REFUTED. The trap is a statically
  emitted `ud2` inside a well-formed block, with the `ok_block` field-load
  sequence at `$rip+2`.
- **Font cache / `clear_ttf` poisoning** — not involved; the fault is upstream of
  any cache access, in candidate selection.

## Fix shape and its hazard (why this was not landed here)

The correct lowering is the one the Simple compiler already implements: branch on
`rt_is_some`, yield `rt_unwrap_or_self(x)` on the present arm and the canonical
nil sentinel on the absent arm, and type the result as the Option's payload type
(attaching struct-name provenance so later field accesses resolve indices).

The hazard that makes this more than a one-liner: `lower_exists_check` has no
position information, and bare `if x.?:` conditions currently rely on the bool.
`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:307` already
special-cases `if val v = expr.?:` by stripping one ExistsCheck layer, but plain
`if expr.?:` still goes through `lower_exists_check`. Switching that to a
value+nil result changes every such condition, and the nil sentinel is not zero
(see the `native_i64opt_some0_collapses_to_nil` note at
`expr_dispatch.spl:2504`), so a naive change makes `if nil_opt.?:` truthy.

A correct fix therefore needs condition-position and value-position lowerings
kept distinct, plus a rebuild of the seed and a re-run of the native smoke matrix
item "(14) Option/nil check (x.?)". That is a scoped compiler change, not a
tail-of-session patch.

**Do NOT work around this by rewriting the library call sites to `if val`.** The
`if val` form does work, but the defect is in the compiler and the library source
is already correct Simple.

## Reproduction commands

```
# minimal (3 s)
bin/simple run <file with the 13-line repro above>     # exit 132

# library path (3 s)
# calls selected_font_asset_for_language_category("en", "sans")
bin/simple run <probe importing std.common.encoding.font_registry>

# full showcase style pass (~10 s)
# parse_html + extract_css_vw + build_child_index + compute_styles(.., true, true)
# on examples/06_io/ui/browser_common_elements_showcase.html   -> exit 132
```

## Fix (landed 2026-07-28)

Position-split lowering in the seed, ported from the interpreter's design:

- `lower_exists_check` (`hir/lower/expr/control.rs`) now lowers **value
  position** to `LetIn($exists_check_subject = expr) { if rt_is_some(subject):
  rt_unwrap_or_self(subject) else: Nil }`, typed as the Option payload (falling
  back to the subject type so the raw-migration struct form keeps its
  struct-name provenance for field-index resolution). The `LetIn` temp makes a
  side-effecting receiver (`f().?`) evaluate exactly once. The absent arm emits
  `HirExprKind::Nil`, which materializes the canonical sentinel `3`, not `0`.
- A new `lower_condition` handles **condition position** and keeps the boolean
  `rt_is_some` predicate there. This is the half the naive fix gets wrong: the
  nil sentinel is non-zero, so branching on the value form would make
  `if nil_opt.?:` truthy — a silent wrong-branch bug, strictly worse than the
  loud SIGILL. Routed through it: `if`/`elif`/`while` conditions,
  `assert`/`assume`/`admit`, guard statements (`? cond -> result`), match
  guards, ternary/if-expression tests, and all boolean contract clauses
  (`decreases` is a measure, not a condition, so it stays on `lower_expr`).
  Only a bare `.?` is intercepted directly; everything else goes through the
  normal `lower_expr` dispatcher and `and`/`or`/`not` operands are then
  post-rewritten structurally, so `if a.? and b.?:` works without bypassing
  the dispatcher (see the perf note below).
- **Bool-return position** — `fn has(..) -> bool: opt.?` — also gets the
  predicate, via `lower_bool_return_expr` for an explicit `return` and a
  structural `coerce_exists_value_to_bool_in_place` rewrite for the implicit
  trailing-expression form. Without this the `T?` value escapes through the
  function boundary and every `if has(..):` caller branches on the non-zero
  nil sentinel — the same wrong-branch bug, just laundered through a return.
  **This is not optional: 42 owned `-> bool` functions return a bare `.?`**
  (about 10 of them inside `src/compiler/` itself — `has_errors`,
  `has_violations`, `is_resolved`, `has_default`, …), and an audit-then-A/B
  proved they all regressed without it. Measured on the seed before the
  coercion was added: `has_some()` returned `<special:7>` instead of `true`,
  `has_none()` returned the nil sentinel instead of `false`, and
  `if has_none():` took the TRUE branch.

This is the same split the interpreter already used (`is_condition_present` in
`interpreter_control.rs` special-cases `Expr::ExistsCheck` at every condition
site while `interpreter/expr.rs` evaluates `.?` to the value).

### Convergence with the `-> bool` report

`doc/08_tracking/bug/option_predicate_returns_payload_not_bool_2026-07-28.md`
reports the same operator from the other end and proposes, as one option,
"lower `.?` to a real bool in both engines". **That option is this bug** — it is
what the seed did, and it is what produced the SIGILL. The spec
(`syntax_quick_reference.md`, "Existence Check (`.?`) — Returns `T?`"), the
interpreter, and the pure-Simple compiler's own type inference
(`src/compiler/30.types/type_system/expr_infer.spl:360`, "`.?` operator returns
`T?`") all agree `.?` yields `T?`. So the correct reading of that report is its
*other* option: a `-> bool` function returning `.?` needs the declared return
type honoured. That is exactly what the bool-return coercion above implements,
which closes that report's seed half. Its remaining half —
`expect(x.?).to_equal(true)` — is simply wrong test code, as that report's own
workaround concluded; `.?` is not a bool and never was.

### Known remaining divergence (INFERRED, not executed)

The **pure-Simple** compiler still lacks the condition-position split. Its
`lower_if` (`src/compiler/50.mir/mir_lowering_stmts.spl:1333`) calls
`self.lower_expr(cond)` with no `ExistsCheck` special case, so a bare
`if opt.?:` there lowers to the value form and branches on the non-zero nil
sentinel — i.e. always true. The `if val v = opt.?:` form is safe because the
parser desugars it to a raw binding plus `v != nil`. This was read from source,
**not executed**, because the pure-Simple compiler is not the deployed binary.
It needs its own fix + bootstrap; filing it is follow-up work, not part of this
change.

Evidence, seed rebuilt from `origin/main` + this change, pre-fix binary =
the deployed `bin/release/x86_64-unknown-linux-gnu/simple`:

| case | pre-fix | post-fix |
|---|---|---|
| 13-line repro (`val u = r1.?` then `u.b`) | exit 132, "field access on nil receiver" | exit 0, `b=P1` / `a=p`, absent case yields nil |
| `resolve_font_metrics_with_language("sans-serif", .., "en")` | exit 132 | exit 0, `width=125` |
| same, CJK content (exercises `:2027` complex-script arm) | exit 132 | exit 0, `width=128` |
| `compute_styles(.., vector_fonts: true)` on the showcase HTML | exit 132 | exit 0, 149 styles |
| condition-position matrix (some/none/not/and/or/while/if-val) | 10 of 11 correct | byte-identical, no regression |
| `-> bool` fn returning a bare `.?`, and its `if has():` caller | correct | correct (identical) |
| native-smoke-matrix item "(14) Option/nil check (x.?)" | `pass=1` | `pass=1`, `codegen_fallback_hits=0` |
| `test/03_system/feature/usage/exists_check_value_return_spec.spl` | 18/18 | 26/26 (6 new condition-position + 2 new value-position cases) |

Engine note: every row above except the last was run through `simple run`
(the Cranelift JIT), which is the lane this defect lives in. `simple test`
hard-defaults to the tree-walk interpreter, so the spec row is interpreter
evidence — the spec is the permanent regression home, but the JIT proof is the
`run` rows.

The downstream `.?` sites at `font_renderer.spl:2015/2017/2027` clear with the
fix — `:2015`/`:2017` are exercised by the Latin probe and `:2027` by the CJK
probe.

Two things this fix does NOT change, both pre-existing and reproduced
identically on the pre-fix binary:

- `if some_i64_opt.?:` on a `Some(0)` payload takes the FALSE branch
  (`native_i64opt_some0_collapses_to_nil`; `rt_is_some` cannot distinguish a
  raw `0` payload from absence). Unrelated to the `.?` return type.
### Perf note (found and fixed inside this change)

A first cut of the condition/bool-return lowering hand-built the `and`/`or`/`not`
HIR instead of going through `lower_expr`. That bypassed the normal dispatcher
and reached a codegen path that emits `rt_index_of`, producing an
`unresolved external symbol 'rt_index_of'` bailout that demoted the whole
browser-engine module to the interpreter — the showcase style pass went from
JIT-compiled to **384 s interpreted**. Routing those forms back through
`lower_expr` and only post-rewriting the lowered `.?` shape removed it; the
final binary runs the showcase with `codegen_fallback_hits=0` and zero JIT
fallbacks. The lesson is recorded here because the symptom (a perf cliff, not a
wrong answer) is easy to ship unnoticed.

**That bailout was NOT an artifact of the first cut — it was a real standing
defect this change merely stopped triggering.** It has since been **fixed
independently** by `5c75a1bbce0` ("fix(jit,runtime): register rt_index_of so
index_of stops de-JITting the module"), which landed both the definition and
the registrations. Verified on a binary built from `origin/main` at
`b410e53a7a2`: `nm … | grep rt_index_of` → 1, and `arr.index_of(30)` → `2`,
`"hello world".index_of("world")` → `6`, `arr.index_of(99)` → `-1`, all
correct. Nothing is outstanding on the JIT lane.

This section went through two wrong revisions before that. Both errors are
recorded because each has a reusable lesson:

1. **"`rt_index_of` is defined" — wrong tree.** Verified against this shared
   working copy, which carried another lane's unpushed definition, while
   `origin/main` had none. A working-copy-only symbol reads exactly like a
   present one. *Verify publishable findings against `origin/main`, and say
   which tree you measured.*
2. **"four codegen paths emit it" — wrong grep.** Only **two** emit the symbol
   (`codegen/instr/calls.rs:3234`, `codegen/instr/closures_structs.rs:1284`).
   The two LLVM sites match the *method name* `"index_of"` but emit
   `rt_string_find` (`llvm/emitter.rs:191`, `llvm/functions.rs:2274`).
   *Grep the emitted symbol (`'"rt_index_of"'`), not the method name.*

**Still open, and measured here (NOT a `.?` issue — handed to the `index_of`
lane):** `index_of` is unsupported on the LLVM/native-build lane. On the same
`b410e53a7a2` binary that is correct under the JIT, `native-build` fails with
`MIR lowering error: unresolved method call: index_of` (rc=1, no binary), while
an otherwise-identical probe without `index_of` native-builds and runs fine.
So the failure is loud, not silent — the hypothesis that the two backends
silently disagree (JIT via polymorphic `rt_index_of`, LLVM via string-only
`rt_string_find` returning the `-1` mismatch sentinel) does **not** reproduce:
MIR lowering rejects the method before either LLVM mapping is reached. This
diagnostic is not the Rust seed's at all — `"unresolved method call"` has zero
hits in `src/compiler_rust/**/*.rs` at `origin/main`; it comes from the
**pure-Simple** compiler. The class is already tracked in
`doc/08_tracking/bug/native_string_methods_unresolved_in_mir_2026-07-17.md`.

### Task #145 const-0 placeholder — the guard is a warning, not a hard fail

The 2026-07-17 doc above *originally* described the Task #145 guard as
"converting unresolved calls into hard errors rather than silently emitting a
placeholder". **That is not what the code does**, and the difference matters
because a const-0 where a value was expected is the same failure shape as the
nil sentinel reading as a real integer — this report's own defect class.
(That doc has since been corrected in `c95282e20d1`, which also scoped its
Medium severity to the two methods it reported and noted that the placeholder
was firing in its own repro transcript all along. The two docs now agree; the
analysis below is kept because it is the evidence.)

At `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2485-2500`
the unresolved path calls `self.error(...)` and then *continues*, emitting the
const-0 placeholder. Its own comment states the problem plainly: `self.error`
**only collects**, and both the bootstrap lane (`driver_bootstrap.spl` reads
`ctx.errors`, never `MirLowering.errors`) and the native-build worker drop that
list, after which the placeholder "ships as SILENT data loss (exit 0, no
stderr) — exactly how the `.join()` no-op survived undetected". The `print`
warning exists precisely because the error alone is not reliably fatal. So
fatality depends on the consumer, not on the guard.

Measured on `b410e53a7a2`, same probe, two lanes:

| lane | const-0 warnings | hard error surfaced | result |
|---|---|---|---|
| `native-build` (default) | 3 | yes (3) | rc=1, no binary — loud |
| `native-build`, `SIMPLE_BOOTSTRAP=1` | 3 | **no (0)** | rc=1, no binary |

The bootstrap lane demonstrably **drops the hard error**, corroborating the
source comment. It is *not* proof that a const-0 ships silently, because that
run died for an unrelated reason before codegen (`error: semantic: function
expects argument for parameter 'span', but none was provided`). So: the
mechanism for silent const-0 is confirmed to exist and one lane is confirmed to
swallow the error; an end-to-end "exit 0 with a wrong value" reproduction is
still **not** demonstrated. That is the open measurement, and it belongs to the
`index_of`/Task #145 lane, not to this `.?` report.

Measurement caveat for anyone re-running these: this host was concurrently
running another session's `stage2_*` jobs holding ~95 GB RSS at load average
34, and the resource monitor SIGTERM'd the probe (exit 143) at 1.3 GB RSS
several times. Those kills are environmental, not a defect — retry on an idle
host.

## Related

- `doc/08_tracking/bug/web_render_budget_interpreter_gap_2026-07-25.md` — the
  interpreted-lane budget gap this defect now sits behind.
- `doc/08_tracking/bug/native_font_acceptance_pre_summary_sigill_2026-07-19.md` —
  earlier exit-132 font acceptance blocker, same `.?`-heavy region.
