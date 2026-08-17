# text.index_of(needle, start) — start argument dropped; run lane leaks the error sentinel as data

- **Filed:** 2026-07-28
- **Status:** OPEN — root-caused, fix NOT contained (needs a new runtime symbol + a semantics decision)
- **Severity:** HIGH — silent wrong answers on both lanes; the `run` lane exits 0 while corrupting an i64
- **Marker to search:** `text_index_of_start_2026-07-28`

## Summary

The two-argument form `s.index_of(needle, start)` on a `text` receiver has **no
implementation anywhere in the toolchain**. There is no offset-aware runtime
symbol at all. Every dispatch path either silently discards the `start`
argument or fails to resolve the call.

The originally reported symptom — "`bin/simple run` cannot call the QEMU
harness cross-module, fails with `Function 'str.index_of' not found` four
times" — is **real but misattributed**. It is not a cross-module defect and not
a name-resolution defect. It is an **arity** defect: the 2-arg form. The "four
times" is simply the four `index_of` call sites in the harness.

## Reproduction (minimal)

`bin/simple` here is the **Rust seed**
(sha256 `e5c461a5f0cba9ba…`, mtime 2026-07-28 12:13:15 UTC,
resolved path `bin/release/x86_64-unknown-linux-gnu/simple`;
per `scripts/check/check-compiler-provenance.shs`).

Module path must avoid digit-leading segments (`test.01_unit.…` fails to parse
as a module path — the segment lexes as `TypedInteger`), so the probe lives
under `test/system/`.

`test/system/zzprobe/lib/h2.spl`:

    fn find2(hay: text, n: text) -> i64:
        hay.index_of(n)

    fn find3(hay: text, n: text, start: i64) -> i64:
        hay.index_of(n, start)

`test/system/zzprobe/m3.spl`:

    use test.system.zzprobe.lib.h2.{find3}

    fn local3(hay: text, n: text, start: i64) -> i64:
        hay.index_of(n, start)

    fn main():
        print("inline-in-main:")
        print("a[P]b[P]c".index_of("[P]", 3))
        print("same-module-fn:")
        print(local3("a[P]b[P]c", "[P]", 3))
        print("cross-module-fn:")
        print(find3("a[P]b[P]c", "[P]", 3))

Correct answer for all three is `5`.

### run lane

    SIMPLE_TIMEOUT_SECONDS=60 ./bin/simple run test/system/zzprobe/m3.spl

Output (EXIT=0):

    inline-in-main:
    Runtime error: Function 'str.index_of' not found
    27
    same-module-fn:
    Runtime error: Function 'str.index_of' not found
    27
    cross-module-fn:
    Runtime error: Function 'str.index_of' not found
    27

All three shapes fail identically. **Cross-module is NOT the axis** — inline in
`main` fails the same way.

### test lane

Same three shapes as a spec, asserting `to_equal(5)`:

    3 examples, 3 failures
    expected 1 to equal 5   (x3)

No error is printed; the answer is just wrong — `start` is ignored and the
first match (index 1) is returned.

### The 1-arg form is fine

`find2` (`hay.index_of(n)`) returns `1` correctly on both lanes. Only the
2-arg form is affected.

## Lane-by-lane behaviour

| Lane | Invocation | Binary actually used | `s.index_of(n, 3)` | Exit |
|---|---|---|---|---|
| run | `bin/simple run m3.spl` | `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed) | prints `Function 'str.index_of' not found`, yields **27** | **0** |
| test | `bin/simple test idx3_spec.spl` | `src/compiler_rust/target/debug/simple` | silently returns **1** (start ignored) | 1 (assert) |
| run, 1-arg | `hay.index_of(n)` | seed | `1` (correct) | 0 |

Note the two lanes run **different binaries**; `simple test` spawns
`src/compiler_rust/target/debug/simple`, reported in its own output as
`child binary:`.

## Root cause — proved sites

**Why `27`.** `rt_function_not_found` at
`src/compiler_rust/runtime/src/value/sffi/error_handling.rs:24` prints the
message and returns `RuntimeValue::from_special(tags::SPECIAL_ERROR)`.
`SPECIAL_ERROR = 3` (`runtime/src/value/tags.rs:13`), and the tagged encoding
`(3 << 3) | 3 = 27`. So **27 is the error sentinel being consumed as an
ordinary i64**. Nothing aborts; the process exits 0 with corrupt data. This is
the dangerous half of the bug — it is invisible to any gate that checks only
the exit status.

**Why the lookup fails (run lane).** `index_of` is typed correctly
(`compiler/src/hir/lower/expr/mod.rs:982` maps it to `TypeId::I64`), but every
codegen mapping binds the name to a **2-parameter** runtime function
(receiver + needle) with no arity discrimination:

- `compiler/src/codegen/instr/closures_structs.rs:1378` — `"index_of" => "rt_index_of"`
- `compiler/src/codegen/llvm/functions.rs:2276` and `:2614`
- `compiler/src/codegen/instr/calls.rs:3235`
- `compiler/src/codegen/llvm/emitter.rs:192`

The registered spec is
`RuntimeFuncSpec::new("rt_string_find", &[I64, I64], &[I64])`
(`compiler/src/codegen/runtime_sffi.rs:415`) — two params. With three
arguments the mapping does not apply, the call degrades to dynamic dispatch by
name, and `rt_function_not_found("str.index_of")` fires. The `str.` prefix is
just the receiver-type-qualified dynamic name; it is **not** evidence of a
module-resolution problem.

**Why it is silently wrong (test lane).**
`compiler/src/interpreter_helpers/method_dispatch.rs:97-103` matches
`_args.first()` (the needle) and **discards any further arguments with no
arity check**, always returning the first match.

**No offset-aware primitive exists.** There is no
`rt_string_find_from` / `spl_str_index_of_from` / `rt_str_index_of_from`
anywhere in `src/runtime/` or `src/compiler_rust/`. The C runtime is 2-param
throughout: `spl_str_index_of(const char* s, const char* needle)`
(`src/runtime/runtime.c:409`, `src/runtime/runtime_legacy_core.c:197`,
declared `src/runtime/runtime.h:119`), and `rt_strfind`
(`src/runtime/runtime_native.c:3640`) forwards to it, structurally unable to
carry a start offset. The only offset-aware `index_of_from` in the tree is a
local compiler-tool helper,
`src/compiler/90.tools/sffi_gen/intern_codegen.spl:62`, not a runtime symbol.

**Self-hosted compiler has the same gap.** In `src/compiler/`, the only
dispatcher that even looks at a second argument is
`10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:131-141`,
and it "implements" the offset by re-calling
`s.index_of(needle, start)` — the very 2-arg form that does not exist,
i.e. it delegates to itself. All other sites are arity-1 only:
~~`interpreter/eval_methods.spl:466-473`~~, `compiler/cg_expr.spl:527-530`
(emits 2-param `spl_str_index_of`), `95.interp/mir_interp_intrinsics.spl:155-163`.

> **Citation dropped 2026-08-01 — conclusion unchanged.** `eval_methods.spl`
> was a dead duplicate shadowed by the `_EvalOps` copies and was deleted in
> `f97dfbbb8ee`; it was never one of the "sites" in the sense this survey
> means, because it never executed. Removing it does not change the finding:
> the sole live 2-arg-aware dispatcher is still
> `_EvalOps/access_literal_assign_eval.spl` (the arm has since moved to
> :243-257 and still delegates to `s.index_of(needle, start)`), and every other
> live site is still arity-1. The self-delegation defect stands.

## A semantics decision is required before any fix

The two lanes do not merely disagree about the offset; they disagree about the
**unit of the returned index**:

- `rt_string_find` (`runtime/src/value/collections.rs:2479`) documents and
  returns a **byte** index.
- `interpreter_helpers/method_dispatch.rs:100` returns
  `s[..idx].chars().count()` — a **character** index.

These coincide only for ASCII. This is the byte-vs-character family already
recorded elsewhere in tracking. Any fix must first settle whether `index_of`
(and therefore `start`) is byte-indexed or character-indexed, because `start`
has to be interpreted in the same unit the function returns. Patching one lane
before settling this would widen the divergence rather than close it.

## Why the fix is not contained

A correct fix spans, at minimum:

1. A new offset-aware runtime primitive in Rust plus its `RuntimeFuncSpec` and
   JIT symbol-manifest registration.
2. A C-runtime counterpart (`runtime.c`, `runtime.h`, `runtime_native.c`).
3. Arity-discriminating mappings at the five codegen sites listed above.
4. `interpreter_helpers/method_dispatch.rs` honouring the second argument.
5. Four dispatch sites in the self-hosted `src/compiler/` tree.
6. The byte-vs-character semantics decision above.
7. A full seed rebuild plus bootstrap to verify, on a machine currently at load
   40-60.

Partial application makes things worse: fixing only the interpreter would leave
codegen returning the `27` sentinel, and fixing only codegen would leave the
`test` lane green on wrong answers.

## Blast radius

- **126** call sites pass a start offset (`.index_of(x, y)`) — 107 in `.spl`
  sources, 19 in docs/tracking. All are exposed: silently wrong on the test
  lane, sentinel-corrupted on the run lane.
- **2396** single-argument `.index_of(x)` sites are unaffected.
- Six files shadow the builtin with a local 3-param
  `fn index_of(text, substring, start)` and are therefore immune:
  `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/http/{common,utilities}.spl`.

Notable affected production sites include
`src/app/editor/gui_shell_core.spl` (5 sites), `src/app/ui.browser/dom_bridge.spl`
(8 sites), `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` (4 sites),
and `src/lib/gc_async_mut/gpu/browser_engine/script/js_transpiler.spl` (3 sites).

### Observed downstream effect

`test/03_system/os/qemu/os/common/qemu_os_harness.spl` uses the 2-arg form at
lines 336, 339, 381 and 393. `count_passes` / `count_failures` (lines 381, 393)
advance with `pos = idx + 6` and loop until `index_of` returns `< 0`. Because
`start` is ignored, the same match is returned forever and the loop **never
terminates**. Reproduced: a cross-module call into this shape under `run` was
killed by the CPU guard at 65s. The harness's `[PASS]`/`[FAIL]` counting is
therefore not trustworthy wherever this path executes.

## Ruled out

- **Cross-module dispatch** — refuted. Inline-in-`main`, same-module function,
  and cross-module function all fail identically (matrix above).
- **Module path spelling** (`test.qemu.…` vs `test.system.qemu.…`) — not the
  cause. `test/system/` and `test/03_system/` are two independent real
  directories, not symlinks (distinct inodes), but the two harness copies differ
  by exactly one unrelated line (`Ok(()): ()` vs `Ok(()): pass_dn`, an
  uncommitted local edit). No `index_of` difference. Separately, `use
  test.01_unit.…` cannot parse at all, which is why the `test.system.…`
  spelling exists.
- **Name resolution / the `str.` prefix** — the prefix is the ordinary
  receiver-type-qualified dynamic-dispatch name produced after codegen mapping
  fails. Resolution is not broken; there is nothing to resolve to.
- **HIR type table** — correct; `index_of` is registered as `TypeId::I64`.
- **JIT fallback masking** — checked with `SIMPLE_JIT_STRICT=1`. Fallbacks seen
  in an early probe were `Unknown variable: helper` from an unrelated
  module-qualified-call lowering gap, not from `index_of`; the final matrix
  reproduces the defect with no `index_of`-related fallback.
- **The off-by-one landed as `19dc65d88be`** — unrelated, as the reporting
  agent judged.

## Suggested regression test (add with the fix)

Assert on both lanes that `"a[P]b[P]c".index_of("[P]", 3)` is `5`, that a start
beyond the last match yields `-1`, and that a start past end-of-string yields
`-1` rather than the sentinel. Assert the exit status too, so the run lane
cannot pass by exiting 0 with a corrupt value.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: ALREADY-FIXED IN 50.mir BY CONTENT.**

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2247` now handles
`method == "index_of" and args.len() == 2`, lowering three operands including
`tf_start` into `rt_text_find` at `:2265-2274`. The `start` argument is no longer
dropped. Not separately verified: the existence/behaviour of the `rt_text_find`
runtime symbol, and the error-sentinel-leak half of this row — both need a
runtime lane this host cannot provide.
