# Rust seed lowers `.?` to a bare bool — value-position `x.?.field` SIGILLs

- **Date:** 2026-07-28
- **Status:** root-caused, PROVEN, not yet fixed (fix is in the Rust seed's HIR lowering)
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

## Related

- `doc/08_tracking/bug/web_render_budget_interpreter_gap_2026-07-25.md` — the
  interpreted-lane budget gap this defect now sits behind.
- `doc/08_tracking/bug/native_font_acceptance_pre_summary_sigill_2026-07-19.md` —
  earlier exit-132 font acceptance blocker, same `.?`-heavy region.
