# `in` returns FALSE for a member that IS present (JIT) — unboxed membership needle

**Date:** 2026-08-01
**Status:** FIXED (all three defects below)
**Severity:** P0 wrong answer — a membership test that silently answers "absent"
skips work in every guard, filter and dedupe built on it.
**Engine:** Cranelift JIT only. The tree-walking interpreter was CORRECT
throughout, which is why no spec caught it: `bin/simple test` hard-defaults to
the interpreter (see `run_vs_test_harness_divergence_2026-07-28.md`).
**Binary under test:** `src/compiler_rust/target/release/simple`, rebuilt from
tip. The pre-fix binary was kept as an explicit control and re-run against the
POST-fix tree, so every delta below is attributable to the code change and not
to source drift.

## Symptom (PROVED)

Under the JIT, `in` answered `false` for a present member whenever the needle
was a raw scalar. Text needles were unaffected — that asymmetry is the
diagnosis.

| probe | expected | JIT before | interpreter before |
|---|---|---|---|
| `2 in [1, 2, 3]` | true | **false** | true |
| `1 in [1, 2, 3]` | true | **false** | true |
| `2.5 in [1.5, 2.5]` | true | **false** | true |
| `true in [true, false]` | true | **false** | true |
| `1 in {1: 10}` | true | **false** | true |
| `0 in [0, 0, 0]` | true | true | true |
| `"world" in "hello world"` | true | true | true |
| `"beta" in ["alpha", "beta"]` | true | true | true |
| `"k1" in {"k1": 10}` | true | true | true |
| `nums.contains(2)` | true | true (see defect 3) | true |
| `if 2 in nums:` | fires | **takes else** | fires |

`0` matched by accident: the zero value is a fixed point of the tag encoding, so
the raw and the tagged form coincide.

`not in` failed differently — branching was right but the VALUE was garbage:

| probe | expected | JIT before |
|---|---|---|
| `("zzz" not in hay).to_text()` | `"true"` | **`"nil"`** |
| `("world" not in hay).to_text()` | `"false"` | **`"0"`** |
| `if "zzz" not in hay:` | fires | fires (correct) |

## Root causes — THREE distinct defects, all in the Rust seed

### 1. The membership needle was passed to `rt_contains` UNBOXED

`src/compiler_rust/compiler/src/codegen/instr/core.rs`, the `BinOp::In |
BinOp::NotIn` arm, called `rt_contains(collection, raw_i64_needle)`.

`rt_contains` (`src/compiler_rust/runtime/src/value/collections.rs:3989`) takes
`RuntimeValue` parameters: for an array it compares each element with
`rt_value_eq`, for a dict it hash-looks-up the key. Both need the needle
*tagged*. A raw `i64` therefore never matched a boxed element.

The `.contains()` / `.has()` / `.contains_key()` path in
`codegen/instr/methods.rs` already boxed it, with a comment saying exactly why —
the operator path simply never got the same treatment. The fix routes `in`
through the same `wrap_value`.

It also uses the **pre-coerce** operands: `coerce_binop_operands` promotes the
other side to float when either side is float, which for `2.5 in floats` would
have converted the collection POINTER to an f64.

### 2. `NotIn` was missing from the HIR BOOL result-type list

`src/compiler_rust/compiler/src/hir/lower/expr/operators.rs:48` listed
`And | Or | Is | In` but not `NotIn`, so a `not in` expression fell through to
`_ => left_hir.ty` and was typed as its LEFT OPERAND (text, for
`"zzz" not in hay`). `.to_text()` then decoded the raw `0`/`1` as a heap handle
and printed `nil`/`0`. Branching still worked, which is why this hid behind
`if x not in y` for so long.

This is the same family as the JIT text-ordering defect fixed in `6469d70eb4e`:
**a value whose static type is not threaded is silently mishandled downstream.**

The `bxor(result, 1)` negation was also replaced with an `icmp`-against-zero,
matching `BinOp::NotEq`: `rt_contains` returns a `u8` whose upper
return-register bits are not guaranteed clear, so xor could leave a value that
is neither 0 nor 1.

### 3. `rt_box_int` / `rt_box_float` DO NOT EXIST in the runtime

`methods.rs` `wrap_value` emitted calls to `rt_box_int` and `rt_box_float`.
Neither symbol is defined anywhere under `src/compiler_rust/runtime` — there is
no `pub extern "C" fn rt_box_int`. The real tagging helpers are `rt_value_int`
and `rt_value_float` (`runtime/src/value/sffi/value_ops.rs:7,11`).

Consequence: any module containing a `.contains(<int>)` hit
`unresolved external symbol 'rt_box_int'` and the JIT **silently dropped the
WHOLE MODULE to the interpreter**, printing
`[jit-fallback] ... whole module dropped to the interpreter (expect ~100-1000x
slowdown)` and **exiting 0**. That is why `nums.contains(2)` looked correct in
the very first probe: that answer came from the interpreter, not the JIT.

This nearly produced a false green for this very fix. The first fixed build
appeared to pass — with the fallback banner in the output. Every verification
below is therefore run under `SIMPLE_JIT_STRICT=1`, which turns the fallback
into a hard error, so a green result is genuinely JIT-executed.

## Fix

- `src/compiler_rust/compiler/src/codegen/instr/core.rs` — box the needle via
  `methods::wrap_value` using the pre-coerce operands; negate `NotIn` with
  `icmp` against zero instead of `bxor`.
- `src/compiler_rust/compiler/src/codegen/instr/methods.rs` — `wrap_value` is
  now `pub(super)`, and emits `rt_value_int` / `rt_value_float` instead of the
  nonexistent `rt_box_int` / `rt_box_float`.
- `src/compiler_rust/compiler/src/hir/lower/expr/operators.rs` — `NotIn` joins
  `In` in the BOOL result-type arm.
- `src/compiler_rust/compiler/src/codegen/common_backend.rs` — `rt_value_int` /
  `rt_value_float` are codegen roots (the `in` arm emits them from a BinOp node,
  which is not a MIR `BuiltinMethod` node), and the stale `rt_box_*` names in
  the `BuiltinMethod` list are corrected.

## Verification

All under `SIMPLE_JIT_STRICT=1` on the rebuilt binary — no fallback banner, so
these are true JIT measurements. Every probe above now answers correctly, and
the true-positive controls that must STAY false still do: `9 in nums`,
`"gamma" in words`, `"zz" in d`, `7 in {1:10}`, `"world" not in hay`,
`9.5 in [1.5, 2.5]`. A fix that merely silenced one engine would have flipped
those too.

Regression spec: `test/01_unit/language/in_operator_membership_spec.spl` —
20 examples, 20 passed. Non-vacuity proved by sabotage: flipping
`assert_true(20 in a)` to `assert_false` gave `20 total, 19 passed, 1 failed`,
exit 1, with the other 19 assertions in the same block staying green; the
sabotage was then reverted.

Focused Rust unit tests (`binop`, `contains`, `box_int`, `box_float`,
`wrap_value`): 99 passed, 0 failed.

`simple test test/01_unit/language` fails identically (`5 total, 0 passed`) on
BOTH the pre-fix control binary and the fixed binary — a pre-existing
directory-run harness problem, not a regression from this change. Individual
spec files run fine.

## Blast radius

**Mechanism-scoped (this is the honest statement of reach):** every `in` /
`not in` in the codebase whose needle is an int, float or bool, on every engine
path that is the Cranelift JIT — which is what a bare `simple <file>.spl` and
`simple run` use. Text needles were never affected, so anything doing substring
or string-set membership was correct all along.

A precise static enumeration of `in` call sites is NOT reliably greppable: `in`
is also the `for ... in` keyword and the most common English preposition, so a
`.spl` sweep for ` in ` returns ~20,000 lines that are overwhelmingly prose in
comments and string literals. The keyword-anchored form (`if`/`while`/`return`/
`and`/`or`/`val =`/`var =` followed by an `X in Y`) finds 13 sites, 2 of them
`not in`, concentrated in `test/03_system` and `test/system` — so **very little
owned code uses the operator form on a scalar needle, and none of it is
load-bearing product code.** Counts taken with `/usr/bin/grep`, excluding
`**/vendor/**`.

Defect 3 has the wider reach, because it is not about answers but about
**performance and engine identity**: `.contains(<numeric literal>)` appears at
601 sites across 115 files (55 under `test/01_unit`, 23 under `test/unit`, 16
under `test/03_system`, 4 under `src/app`). Every one of those modules was
running fully interpreted under the JIT, at the documented 100-1000x penalty,
with exit code 0 and only a stderr banner to say so. Any perf measurement taken
on such a module was measuring the interpreter.

## Not fixed here (filed, adjacent)

- **`x in <range>` diverges between engines.** The JIT now answers `3 in 1..5`
  → true / `9 in 1..5` → false, but the INTERPRETER rejects it outright:
  `semantic: 'in' operator requires array, tuple, dict, or string; got object`.
  One of the two is wrong about whether ranges are a membership receiver at all.
  This is a spec question, not a codegen bug, so it is left for a language
  decision rather than settled unilaterally here.
- **The LLVM backend still emits `rt_box_float`** — RESOLVED, see
  "Predicted sibling: LLVM backend" below.
- **`//` at the start of an indented block body lexes as a `Parallel` token**,
  not a comment: `fn main():` followed by an indented `// note` line fails with
  `Unexpected token: expected Indent, found Parallel`. Found incidentally while
  writing the probes; unrelated to `in`.

## Follow-up: `rt_array_map` / `rt_array_each` / `rt_array_reduce` — FIXED

The sibling this fix's family predicted (see the `rt_box_float` bullet above)
turned out to have a larger relative: **three array collection ops the LLVM
backend emits existed in NEITHER runtime**, so `arr.map(f)`, `arr.each(f)` /
`arr.for_each(f)` and `arr.reduce(init, f)` / `arr.fold(init, f)` all failed at
LINK time under the LLVM backend.

**Emitter-operand check FIRST (the gate that decides whether a symbol may be
implemented at all).** A missing symbol must stay a loud link error whenever its
emitter discards its own operands — implementing it would trade a loud failure
for a silently wrong answer. Both LLVM emitter sites
(`codegen/llvm/functions.rs`) build the arg list as `receiver + args` verbatim
via `get_vreg` + `coerce_value_to_type`, dropping nothing:

| symbol | emitted call | operands faithful? | verdict |
|---|---|---|---|
| `rt_array_map` | `(array, closure)` | yes | implement |
| `rt_array_each` | `(array, closure)` | yes | implement |
| `rt_array_reduce` | `(array, init, closure)` | yes | implement |
| `rt_par_map` / `rt_par_filter` / `rt_par_for_each` | emitter passes 2, spec declares 4 (`input_len` and `backend` dropped) | **NO** | leave loud |
| `rt_par_reduce` | emitter passes 3, spec declares 5 | **NO** | leave loud |

**Family enumeration (PROVED).** Every `rt_*` string in
`compiler/src/codegen/**` diffed against the union of symbols defined in both
runtime sources: on the array-collection-op axis exactly three names had no
definition anywhere. `rt_index_of` and `rt_string_lines` showed as missing only
against a *stale* archive and do exist in source — a reminder that archive-only
absence must be confirmed against source. Everything else on that missing list
is the latent-placeholder set (`rt_enum_unit`, `rt_pattern_test`,
`rt_future_create`, …) whose emitters discard operands, plus the `rt_par_*` set
above. None of those were implemented, deliberately.

**Argument order is pinned to the interpreter, not guessed.** `reduce`/`fold`
take `(init, func)` (`interpreter_method/collections.rs`) and invoke the
function as `(acc, item)` (`interpreter_helpers/collections.rs`), so the
runtime signature is `rt_array_reduce(array, init, closure)` with a
three-parameter lifted target `func(closure, acc, item)`. Both are verified with
a **non-commutative** fold (`acc*10 + item`), which a transposed order would
answer differently.

### Link-level evidence (codegen proves nothing; only the linker does)

Absence was established against **built archives**, not source: `nm
--defined-only` over both (1,637 exported `rt_*` in the Rust archive, 790 in the
C one), with a true-positive control of nine known-real symbols to prove the
scan works. All three targets: absent from both.

Discrimination was RED-before-GREEN by sabotaging the **implementation** — the
probe was linked against the runtime object built from the *base* sources, not
against a shim or a stubbed test:

| runtime | link vs BASE impl | link vs NEW impl |
|---|---|---|
| C (`runtime_native.c`) | rc=1, `undefined reference to 'rt_array_map' / '…each' / '…reduce'`, **no artifact** | rc=0 |
| Rust (`libsimple_runtime.a`) | rc=1, same three undefined, **no artifact** | rc=0 |

Positive artifact check on both GREEN builds: `file` reports an ELF 64-bit
executable; `nm` resolves all three at real addresses (C static: `T rt_array_map
@ 0x40241e`, `rt_array_each @ 0x4024a2`, `rt_array_reduce @ 0x402500`); and the
binaries were **run**. Both runtimes produced byte-identical output —
`map len=3 [10,20,30]`, receiver unmutated, `each side_sum=6` returning the
receiver, `reduce init=7 -> 7123`, and the empty-array and non-closure edges
returning the seed rather than crashing or lying.

`nm -u` was not used as evidence anywhere: it is blind to weak zero-size
definitions, and "no undefined symbols" is not proof.

### Residuals recorded, not silently resolved

- **`rt_array_any` / `rt_array_all` have an arity divergence.** — **FIXED in
  `f835ee71522`** (Rust runtime) and **`9b5661528a9`** (C runtime). See
  "Residual sweep: the three array-op residuals" below.
- **The C runtime has no `filter`/`find`/`any`/`all` at all.** — **FIXED in
  `9b5661528a9`.** See below.
- **Cranelift routes `.map()` to `rt_option_map`** with a comment claiming it
  "also works for arrays". — **The comment was WRONG and is now corrected; the
  misroute is FIXED.** See below.
- **`codegen/runtime_sffi.rs` has a pre-existing duplicate spec** for
  `rt_dir_exists` (two byte-identical entries), which fails
  `codegen::runtime_sffi::tests::all_funcs_have_unique_names`. Present at both
  `e2240ed88cd` and `dcdde4c0a96` with this change absent; not introduced and
  not absorbed here.
- **`simple-runtime --lib` has 7 pre-existing failures** (executor thread spawn
  ×2, package manifest trailer, native lib manager, dict invalid value, low-heap
  tagged values, heap owner attribution). Identical list and identical
  `1080 passed; 7 failed` at base sha `e2240ed88cd`.

## Residual risk

`wrap_value` boxes based on `ctx.vreg_types`, i.e. STATIC type information. A
needle whose vreg type was never threaded falls through to the `_ => val`
pass-through and would still be passed raw — the exact fail-open shape that
caused the text-ordering defect in `6469d70eb4e`. It is not reachable from any
probe written here (literals, `val`-bound scalars, and dict keys all carry their
type), but it is the place this defect would come back.

## Predicted sibling: LLVM backend (FIXED 2026-08-01)

The sibling predicted above was live. It is now fixed, and the sweep it forced
turned up a much larger backlog that is the real deliverable.

### 1. Symbol absence — PROVED, both runtimes

Checked with `git grep` against remote sha
`5d58d58ef16a6603c37e5b6bb64919205df68565` (not `find`/`ls` on disk):

| symbol | Rust runtime `src/compiler_rust/runtime` | C runtime `src/runtime/runtime_native.c` |
|---|---|---|
| `rt_box_int` | 0 definitions, 0 mentions | 0 definitions (1 stale comment) |
| `rt_box_float` | 0 definitions, 0 mentions | 0 definitions |
| `rt_unbox_float` | 0 definitions, 0 mentions | 0 definitions, 0 mentions |
| `rt_value_float` | `pub extern "C" fn rt_value_float(f: f64) -> RuntimeValue` | `int64_t rt_value_float(int64_t raw_bits)` |
| `rt_value_as_float` | `pub extern "C" fn rt_value_as_float(v: RuntimeValue) -> f64` | `double rt_value_as_float(int64_t value)` |

This confirms the `rt_at`/`rt_array_at` precedent does NOT apply here: these are
absent from BOTH runtimes, not just one, so the native lane was not uniquely
exposed.

### 2. What the LLVM path actually did — MEASURED, not inferred

Severity was one of three: hard link error, fabricated weak zero-size
definition, or silent fallback. Measured, it is the **hard link error**:

- Real IR was captured from the backend (a temporary dump harness, since
  removed) for `riscv32-unknown-none-elf`, then run through `llc-18` directly.
- `llc-18` returns **rc=0 for both the broken and the fixed symbol names** and
  emits a real `ELF 32-bit LSB relocatable, UCB RISC-V` object. Codegen itself
  never complains — `nm -u` simply lists the symbol as `U`. So a codegen-only
  check can never see this defect.
- Linking with `ld.lld-18` against an object defining only the symbols that
  really exist is what separates them:
  - pre-fix: `link_rc=1`, `ld.lld-18: error: undefined symbol: rt_box_float`
  - post-fix: `link_rc=0`, positive artifact — `ELF 32-bit LSB executable, UCB
    RISC-V, statically linked`, with `nm` showing `rt_value_float` and
    `rt_value_as_float` resolved at real addresses.
- The weak-zero-size-stub possibility was checked and ruled out on this path:
  `check_no_fabricated_extern_definitions`
  (`linker/native_binary/stubs.rs:520`) deliberately SKIPS freestanding targets
  (`TargetOS::Any | None | SimpleOS`), delegating to the per-entry ratchet in
  `pipeline/native_project/stubs.rs` backed by
  `config/freestanding_fabricated_stub_baseline.sdn`. Neither `rt_box_float` nor
  `rt_unbox_float` appears in that baseline, so a fabricated stub for them would
  be NEW and would fail the ratchet rather than link quietly.

**Consequence:** unlike the Cranelift/JIT half — which silently dropped whole
modules to the interpreter at 100-1000x and exited 0 — the LLVM half was
*unbuildable*, and only on 32-bit targets. `build_box_float_value` /
`build_unbox_float_value` return early on the inline shift/or path when
`runtime_int_type()` is 64-bit, so only `pointer_width() == 32` (riscv32 /
SimpleOS) reached the call. It is therefore INFERRED that no 32-bit SimpleOS
build ever executed `MirInst::BoxFloat`, or it would have failed loudly.

### 3. Fix

`codegen/llvm/functions.rs`, matching the Cranelift fix in
`codegen/instr/methods.rs`:

- `rt_box_float` → `rt_value_float`
- `rt_unbox_float` → `rt_value_as_float`

### 4. The IR test was REPLACED, not relaxed

`test_riscv32_float_boxing_uses_runtime_helpers` asserted
`ir.contains("call i32 @rt_box_float(double")` and
`ir.contains("call double @rt_unbox_float(i32")` — it pinned the defect, the
same shape as the `"error"`-sentinel unit tests replaced earlier the same day.
Those two assertions were **replaced** with assertions naming the helpers that
exist in both runtimes, plus explicit negative assertions so the dead names
cannot return. A true-positive control was added alongside it,
`test_x86_64_float_boxing_is_inline_not_a_runtime_call`, so that "no
`rt_box_float` in the IR" cannot be satisfied by the boxing path going silent
instead of being fixed.

Verification note. `cargo test -p simple-compiler --features llvm --lib
codegen::llvm::` gives 22 passed / 1 failed. The one failure,
`rt_value_bool_calls_receive_raw_boolean_bits`, is **PROVED pre-existing**: it
was re-run against the unmodified source at the base sha and failed identically
there, so it is not attributable to this change and is not absorbed by it. It
concerns `rt_value_bool` on x86_64, a different path from float boxing.

### 5. Sweep: the LLVM backend emits ~29 MORE runtime symbols that exist in NEITHER runtime

This diff appears never to have been done before. Cross-referencing every
`rt_*` literal in `codegen/llvm/` against every exported symbol in both runtimes
(1,778 Rust `extern "C"` + 1,186 C definitions; `/usr/bin/grep` pinned, and the
extraction validated with a true-positive control on `rt_value_int`,
`rt_value_float`, `rt_array_push`, `rt_dict_get`, `rt_array_len`, all non-zero):

Emitted via `emitter.rs` `call_runtime` / `call_runtime_void`, **defined
nowhere**, and reachable — each has a corresponding `MirInst` that lowering
actually produces (site counts in parentheses):

`rt_contract_check` (20), `rt_result_ok` (9), `rt_option_some` (5),
`rt_future_create` (4), `rt_pointer_new` (4), `rt_pattern_test` (3),
`rt_par_map` (2), `rt_fstring_format` (2), `rt_union_wrap` (2),
`rt_vtable_lookup` (0), plus `rt_coverage_condition`, `rt_coverage_decision`,
`rt_coverage_path`, `rt_enum_unit`, `rt_enum_with`, `rt_generator_create`,
`rt_generator_yield`, `rt_option_none`, `rt_par_filter`, `rt_par_for_each`,
`rt_par_reduce`, `rt_pattern_bind`, `rt_pointer_deref`, `rt_pointer_ref`,
`rt_result_err`, `rt_try_unwrap`, `rt_union_discriminant`, `rt_union_payload`,
`rt_unit_bound_check`.

Also emitted from the method-name mapping table in `functions.rs`:
`rt_array_map`, `rt_array_each`, `rt_array_reduce`. And referenced by name in
sffi dispatch: `rt_dict_contains_key`, `rt_typed_bytes_u8_at`,
`rt_typed_bytes_u8_set`, `rt_typed_bytes_u32_le_unchecked`.

Ruled out as false positives (LLVM *value* names passed to `build_phi` /
`build_left_shift` / `build_call`, or a test module name — not callee symbols):
`rt_len_inline`, `rt_pool_join_tagged`, `rt_redirect`, `rt_value_bool_raw_bits`.

These are NOT 32-bit gated — unlike `rt_box_float` they fire on every target
that goes through the LLVM backend. They are left unfixed here deliberately:
each needs a real runtime-implementation decision (implement the helper vs.
lower the instruction differently), not a rename. Filed as the follow-up this
sweep exists to produce.

### 6. Residual: `rt_value_float` has DIVERGENT signatures between the two runtimes

Not introduced by this fix, but exposed by it and worth recording. The Rust
runtime takes an `f64` (`rt_value_float(f: f64)`); the C runtime takes the raw
bit pattern as an integer (`int64_t rt_value_float(int64_t raw_bits)`) and
returns `int64_t`. The emission here passes `double`, matching the Rust runtime
and the Cranelift fix. On a 32-bit target the C runtime's `int64_t` return also
cannot fit the `i32` tagged `RuntimeValue`. The 32-bit tagged-float
representation is under-specified across the two runtimes; a build that actually
links the C runtime on a 32-bit target would need this reconciled first.

## Disposition of the 36-symbol sweep (2026-08-01, follow-up lane)

The sweep in §5 above was reproduced independently and then dispositioned per
symbol. Reproduction agreed exactly: cross-referencing every `rt_*` token in
`codegen/llvm/` against both runtimes yields 54 raw hits, of which 18 are
non-callees (Rust locals `rt_args`/`rt_fn`/`rt_func`/`rt_name`/`rt_fn_name`/
`rt_enum_disc`, LLVM *value* names `rt_len_inline`/`rt_pool_join_tagged`/
`rt_redirect`, error-message strings `rt_bytes_le_at`/`rt_typed_bytes_le_at`/
`rt_typed_words_at`/`rt_string_substring`, prefix fragments `rt_builtin_`/
`rt_fault_`, test names `rt_value_bool_raw_bits`/
`rt_value_bool_calls_receive_raw_boolean_bits`, and `rt_unbox_float` which now
survives only inside the previous lane's NEGATIVE assertions). That leaves the
same 36 real candidates.

### Absence re-established at the BINARY level — PROVED

The previous lane established absence by `git grep` at a remote sha. That was
re-done one layer lower, against the **built artifacts**, which cannot be fooled
by a definition my regex failed to shape-match:

- `nm --defined-only src/compiler_rust/target/release/libsimple_runtime.a` →
  1,679 exported `rt_*`
- `nm --defined-only build/simple-core/libsimple_runtime.a` → 790 exported `rt_*`
- **All 36 candidates are absent from both.**
- True-positive control: `rt_value_int`, `rt_value_float`, `rt_array_push`,
  `rt_dict_get`, `rt_array_len`, `rt_dict_contains`, `rt_coverage_path_probe`,
  `rt_enum_new`, `rt_generator_next` are all PRESENT. Without this control an
  extraction bug would report every symbol as missing.

### Link-level discrimination — PROVED, and it is the only layer that sees it

Same method as the `rt_box_float` fix, applied against the real Rust runtime
archive rather than a synthetic object:

| probe | result |
|---|---|
| object referencing `rt_coverage_path` | `rc=1`, ``undefined reference to `rt_coverage_path' `` |
| object referencing `rt_path_probe` | `rc=0`, ELF 64-bit executable, `nm` shows `T rt_path_probe` at `0x8fa90` |
| object referencing `rt_dict_contains_key` | `rc=1`, ``undefined reference to `rt_dict_contains_key' `` |
| object referencing `rt_dict_contains` | `rc=0`, ELF 64-bit executable, `nm` shows `T rt_dict_contains` at `0x3050a0` |

Compilation never discriminates; only linking does.

### CORRECTION to the premise: 29 of the 36 are LATENT, not live — PROVED

§5 said these are "reachable — each has a corresponding `MirInst` that lowering
actually produces", and inferred from that that they fire on every LLVM target.
The first half is true; the conclusion is **not**, and this is the single most
important finding of this lane.

`MirInst` lowering does produce these instructions. But the LLVM backend has TWO
instruction paths, and the one containing these emissions is almost entirely
unreachable:

- `codegen/llvm/functions.rs` `compile_instruction` is the real body compiler.
  It has its own arm for every one of these instructions — verified individually
  for `OptionSome`, `OptionNone`, `ResultOk`, `ResultErr`, `ContractCheck`,
  `PatternTest`, `EnumUnit`, `EnumWith`, `UnionWrap`, `PointerNew`,
  `FutureCreate`, `GeneratorCreate`, `ParMap`, `TryUnwrap`, `FStringFormat`,
  `MethodCallVirtual`, `UnitBoundCheck`.
- `codegen/llvm/emitter.rs` (`LlvmEmitter`, the `CodegenEmitter` impl) is reached
  **only** through `compile_emitter_simd_instruction`, whose sole caller is
  `functions.rs:1116` — a match arm listing **`Vec*` SIMD instructions only**.
- The three coverage probes never even get that far: `functions.rs:1739` handles
  `DecisionProbe | ConditionProbe | PathProbe` as an explicit no-op
  ("Coverage instrumentation not yet implemented").

So the ~29 `emitter.rs` emissions are a **latent** landmine, not a live outage.
They arm the moment anything routes a non-`Vec*` instruction through
`LlvmEmitter`. The genuinely live breakage is much smaller — see the table.

### Third spelling found

`codegen/common_backend.rs:428-434` declares the codegen roots for these MIR
instructions as `rt_decision_probe` / `rt_condition_probe` / `rt_path_probe`.
Those three **do exist** in the Rust runtime. So the repo held three spellings of
one concept: the correct one in the roots list and in Cranelift
(`codegen/instr/coverage.rs`), and a dead one in `emitter.rs`.

### Per-symbol disposition (all 36)

**(a) FIXED — renamed to the symbol that exists.** Landed in `9349ff9`.

| symbol | now emits | path | note |
|---|---|---|---|
| `rt_dict_contains_key` | `rt_dict_contains` | **LIVE** | exported by both runtimes; `Dict.contains_key` under LLVM previously failed at link |
| `rt_coverage_path` | `rt_path_probe` | latent | exact arity/order match |
| `rt_coverage_decision` | `rt_decision_probe` | latent | **+ operands reordered** |
| `rt_coverage_condition` | `rt_condition_probe` | latent | **+ operands reordered** |

The reorder is not cosmetic. The runtime takes
`rt_decision_probe(decision_id: u64, result: bool)` and
`rt_condition_probe(decision_id: u64, condition_id: u32, result: bool)` — ids
first, result last, which is how Cranelift passes them — while `emitter.rs`
passed `result` FIRST. Renaming alone would have converted a loud link error
into a silently transposed call.

**(FALSE POSITIVE) — not backend-emitted callees at all (3).**
`rt_typed_bytes_u8_at`, `rt_typed_bytes_u8_set`,
`rt_typed_bytes_u32_le_unchecked` appear in `functions/calls.rs` as
`if sffi_name == "..."` guards that trigger **inline expansion** and return
early. They match an incoming user-declared `@extern` name; the backend never
emits them as callees. No action.

**(b) NEEDS RUNTIME IMPLEMENTATION — live path, no equivalent exists (3).**
`rt_array_map`, `rt_array_each`, `rt_array_reduce`, from the method-name mapping
table in `functions.rs` (the LIVE path, same table as the `Dict` entry above).
The runtime exports `rt_array_filter`, `rt_array_find`, `rt_array_any`,
`rt_array_all` — closure-taking helpers — but **no** `map`/`each`/`reduce`/
`fold`. So `arr.map(f)` / `arr.each(f)` / `arr.reduce(f)` currently fail at LINK
under the LLVM backend. This is a real gap and the highest-value remaining item;
it is a genuine runtime feature addition (closure invocation), not a rename, so
it is filed rather than guessed at here.

**(c) LATENT placeholder lowerings — 26.**
`rt_contract_check`, `rt_option_some`, `rt_option_none`, `rt_result_ok`,
`rt_result_err`, `rt_try_unwrap`, `rt_pattern_test`, `rt_pattern_bind`,
`rt_enum_unit`, `rt_enum_with`, `rt_union_wrap`, `rt_union_payload`,
`rt_union_discriminant`, `rt_pointer_new`, `rt_pointer_ref`, `rt_pointer_deref`,
`rt_future_create`, `rt_generator_create`, `rt_generator_yield`,
`rt_fstring_format`, `rt_vtable_lookup`, `rt_unit_bound_check`, `rt_par_map`,
`rt_par_filter`, `rt_par_reduce`, `rt_par_for_each`.

These are NOT simply "a helper that needs writing". Read the emitter bodies: they
**discard their own semantic operands**.

- `emit_enum_unit(dest, _enum_name, _variant_name)` calls
  `rt_enum_unit(i64_const(0))` — a literal constant. Every unit variant of every
  enum would produce the same value.
- `emit_pattern_test(dest, subject, _pattern)` calls `rt_pattern_test(subj)` —
  the pattern is dropped, so the test tests nothing.
- `emit_union_wrap`, `emit_future_create`, `emit_generator_create` and the rest
  follow the same shape.

Implementing a runtime helper behind these would convert a link error into a
**silently wrong answer**, which is strictly worse. Their correct disposition is
therefore: either thread the real operands and lower properly, or make the
emitter return a hard `Err` so a future routing change fails loudly at compile
time instead of emitting a call to a symbol that does not exist. Not done in
this lane because it is a behaviour decision across 26 methods, and because
nothing reaches them today.

Note for whoever takes them: several LOOK like renames and are not.
`rt_enum_unit`/`rt_enum_with` → `rt_enum_new(enum_id: u32, discriminant: u32,
payload)` needs ids the emitter never receives; `rt_future_create` →
`rt_future_new(body_func, ctx)` and `rt_generator_create` →
`rt_generator_new(body_func, slots, ctx)` are arity mismatches against a single
`block_id` argument. `rt_pattern_*`, `rt_union_*`, `rt_pointer_*`, `rt_par_map/
filter/reduce/for_each` and `rt_fstring_format` have no counterpart of any name
in either runtime.

### Residual (recorded, not silently resolved)

`call_runtime_void` declares every parameter as `runtime_int_type()` (i64 on
64-bit) regardless of the real signature, so the three probe calls now declare
`void(i64, i64[, i64])` against runtime symbols taking `(u64, u32)` /
`(u64, u32, bool)`. The low bits are correct on the SysV and AArch64 ABIs the
values actually travel over, and this predates and outlives the rename, so it is
recorded rather than papered over — the same treatment §6 gives the divergent
`rt_value_float` signature.

### Verification for the landed change

- `cargo test -p simple-compiler --features llvm --lib codegen::llvm::` →
  **24 passed, 1 failed**.
- The one failure, `rt_value_bool_calls_receive_raw_boolean_bits`, is **PROVED
  pre-existing**: the two touched files were reverted to their base-sha content
  and the suite re-run, giving **22 passed / 1 failed** with that identical test
  failing. It is a different path (`rt_value_bool` on x86_64) and is not absorbed
  into this result. It remains open — see §4 above, where the previous lane
  recorded it independently.
- Two regression guards added, each pairing negative assertions ("the dead name
  is gone") with positive ones ("the real emission is still there"), so deleting
  an emission cannot satisfy them — the same true-positive-control discipline as
  `test_x86_64_float_boxing_is_inline_not_a_runtime_call`. Both search only the
  non-test region of their file so they cannot match their own text.
- **Non-vacuity PROVED by sabotage of the implementation, not a shim:** the four
  callee names were reverted (and the two operand orders un-swapped) with the
  test bodies left untouched; both guards went RED. Restoring turned them GREEN.

## Residual sweep: the three array-op residuals (2026-08-01, follow-up lane)

The three residuals recorded under "Residuals recorded, not silently resolved"
were each a genuine silent wrong answer, not a missing feature. All three are
now closed. Landed across `f835ee71522` (Rust `any`/`all`), `9b5661528a9`
(C-runtime parity) and the `rt_map` commit below.

### Emitter-operand verification FIRST, per symbol (the gate)

A symbol may only be implemented once its emitters are shown to pass their
operands faithfully. An emitter that DISCARDS operands must keep failing
loudly — giving it a receiver converts a link error into a silently wrong
answer. Re-verified independently this lane:

| symbol | dispatch sites | emitted call | operands faithful? | verdict |
|---|---|---|---|---|
| `rt_array_any` | `llvm/functions.rs` ×2 (blind + `("Array","any")`), `llvm/emitter.rs`, Cranelift `instr/calls.rs` + `instr/closures_structs.rs` | `(array, closure)` | yes — both LLVM sites build `receiver + args` verbatim via `get_vreg` + `coerce_value_to_type` | implement |
| `rt_array_all` | same five | `(array, closure)` | yes | implement |
| `rt_array_filter` | same five | `(array, closure)` | yes | implement |
| `rt_array_find` | `llvm/functions.rs` ×2, Cranelift ×2 | `(array, closure)` | yes | implement |
| `rt_par_map` / `rt_par_filter` / `rt_par_for_each` | `llvm/emitter.rs` | emitter passes **2**, `runtime_sffi.rs` declares **4** (`input_len` and `backend` DROPPED) | **NO** | **left loud, deliberately** |
| `rt_par_reduce` | `llvm/emitter.rs` | passes **3**, declares **5** | **NO** | **left loud, deliberately** |

The `rt_par_*` verdict was re-verified this lane rather than inherited. They
remain undefined in both runtimes and must stay that way until their emitters
thread the real operands.

### 1. `any` / `all` — the predicate was never applied (FIXED)

`rt_array_any(array) -> i64` had **no closure parameter** while every one of the
five dispatch sites emitted `(array, closure)`. The predicate operand was
accepted by the ABI and then discarded, and the body forwarded to
`rt_array_any_truthy`. The predicate was never invoked even once.

Wrong in BOTH directions, so no "mostly right" reading survives:

| receiver | predicate | before | after (= interpreter) |
|---|---|---|---|
| `[1,2,3]` | `x > 10` | `any=1 all=1` | `any=0 all=0` |
| `[0,0,0]` | `x == 0` | `any=0 all=0` | `any=1 all=1` |

Semantics pinned to the interpreter (`interpreter_helpers/collections.rs`
`eval_array_any` / `eval_array_all`), not guessed: predicate takes the element
alone, iteration short-circuits on the first decisive element, empty receiver is
`false` for `any` and vacuously `true` for `all`.

The zero-predicate spelling is a SEPARATE symbol, not a defaulted argument:
`arr.all_truthy()` lowers to `rt_array_all_truthy(array)` through its own MIR
arm, so no caller reaches these with one operand. This is the same rule as
`substr`: an INT slot cannot carry an optional argument, because the tagged nil
sentinel *is* the integer 3.

### 2. C-runtime parity — six symbols, not four (FIXED in `9b5661528a9`)

The gap was wider than recorded. The Rust runtime defined `rt_array_filter`,
`rt_array_find`, `rt_array_any`, `rt_array_all` **and** `rt_array_any_truthy` /
`rt_array_all_truthy`; the C runtime defined **none of the six**, while already
defining `map`/`each`/`reduce` from `4fbe8c5bb40`.

Absence established against BUILT objects with a true-positive control —
`rt_array_map` / `rt_array_each` / `rt_array_reduce` / `rt_array_get` /
`rt_closure_func_ptr` all present at 1, the six at 0, out of **738** `rt_*`
symbols defined in `runtime_native.c` (vs **1,705** `T rt_*` in the Rust
archive) — then confirmed at source level across every `src/runtime/*.c`,
because archive-absence alone is not proof (`rt_index_of` / `rt_string_lines`
previously looked missing against a stale archive and do exist).

Link-level evidence, never codegen:

| link | result |
|---|---|
| probe vs runtime object built from **BASE** sources | `rc=1`, exactly the six `undefined symbol`, **no artifact** |
| probe vs the **NEW** object | `rc=0`, `file` reports ELF 64-bit executable, `nm` shows all six at real addresses, and it RUNS |

25 of 25 printed values match HAND-COMPUTED expectations: both directions of the
discarded-predicate defect, short-circuit call counts of 1/2/2/3, empty-receiver
vacuity, nil/false/int-0/heap-object truthiness, and the non-array receiver
answering 0 for BOTH `_truthy` forms rather than the vacuous `true` an empty
loop yields. `nm -u` was used nowhere — it is blind to weak zero-size
definitions.

Non-vacuity proved by sabotaging the **implementation**: restoring the
predicate-discarding body turns 8 checks RED with the predicate call count at 0.

`rt_core_value_truthy` mirrors Rust's `RuntimeValue::truthy()` branch for
branch, float test FIRST, because a heap-boxed `0.0` carries `TAG_HEAP` and
would otherwise read as "truthy because the pointer exists".

### 3. `.map()` misrouted to `rt_option_map` — the in-tree comment was WRONG

The comment at `codegen/instr/closures_structs.rs` claimed `rt_option_map`
"also works for arrays since rt_option_map checks if the value is an enum with
Some/None". **It does not**, and the failure is silent rather than loud.
Traced through the actual bodies:

- `rt_is_none(array)` is false — an array is not an Option enum — so the early
  return does not fire;
- `rt_enum_payload(array)` takes `get_typed_ptr::<RuntimeEnum>(_,
  HeapObjectType::Enum)`, which fails on an Array and returns **NIL**;
- the closure is invoked **exactly once**, on that NIL, and the result is
  wrapped in `Some`.

So `[1,2,3].map(f)` answered `Some(f(nil))` — one call instead of three, on a
value never in the receiver, boxed in an Option the source never asked for, with
no error and exit 0. MEASURED, not inferred, both routes in one binary:

| probe | `rt_option_map(array,f)` (old route) | `rt_map(array,f)` (new) |
|---|---|---|
| closure call count | **1** | 3 |
| argument the closure saw | **nil (3)** | 1, 2, 3 |
| result is a `Some` | **yes** | no (an array) |
| result length | **-1** (not an array at all) | 3 |
| result elements | — | `[2,4,6]` |

The **LLVM** `emitter.rs` type-blind table had the identical arm, so this was
never Cranelift-only. The type-AWARE table in `llvm/functions.rs` already routed
`("Array","map")` to `rt_array_map` correctly and is untouched.

**Fix:** a receiver-polymorphic `rt_map`, in the same shape as the in-tree
`rt_at` and `rt_index_of` precedents — arrays go to `rt_array_map`, everything
else keeps its exact previous `rt_option_map` result. The test is done in the
runtime because both misrouting sites dispatch purely on method name;
`try_compile_builtin_method_call` does not even take a receiver type. Option
behaviour is verified UNCHANGED (`Some(5)` → `Some(10)` with one call, `None`
returned unchanged with zero calls, raw nil passed through), so the fix cannot
have bought the array answer with an Option regression. 19 of 19 hand-computed
values match; the comment is corrected at both sites.

### Value-level comparison earned its keep — TWICE

Both probes compared printed values against hand-computed expectations rather
than against another engine, and each caught one of MY OWN wrong expectations
that an engine-vs-engine comparison would have scored PASS:

1. `all(x<2)` over `[1,2,3]` short-circuits after **2** predicate calls, not 1 —
   `x<2` is truthy at 1 and falsy at 2, so the first FALSY element is the
   second. (Implementation was right; my arithmetic was wrong.)
2. `rt_array_len` on a non-array answers **-1**, not 0 — the `as_typed_ptr!`
   bail-out default. The real value is the stronger statement anyway.

### Left deliberately loud (do NOT implement receivers for these)

- **`rt_par_map` / `rt_par_filter` / `rt_par_for_each`** — emitter passes 2
  operands, spec declares 4; `input_len` and `backend` are DROPPED.
- **`rt_par_reduce`** — passes 3, declares 5.

Verified again this lane. Undefined in both runtimes, and they must stay that
way: an emitter that discards operands must keep failing loudly.

### Enumerated sibling found and NOT fixed — `.find()` on an array

Enumerating the family turned up a fourth misroute of the same shape, which is
recorded rather than guessed at:

- `codegen/instr/calls.rs` contains **two** `"find"` arms in one `match`:
  `"find" | "find_str" => Some("rt_string_find")` earlier, and
  `"find" => Some("rt_array_find")` later. First-match-wins in Rust, so the
  array arm is **unreachable** and every array `.find(pred)` on the type-blind
  Cranelift path takes the string route.
- `instr/closures_structs.rs` and `llvm/emitter.rs` both map the bare name
  `find` to `rt_string_find` unconditionally, with no array arm at all.

This is NOT fixed here because it is not the same fix as `rt_map`. Array `find`
returns the ELEMENT while text `find` returns an INDEX (a raw `i64`, not a
tagged value), so a polymorphic `rt_find` would have to change the text return
shape — trading a known wrong answer on one receiver for a possible new one on
the other. It needs a return-type decision, not a rename.

### Signature divergence recorded, not silently reconciled

The C entry points take `SplArray*` and raw pointers where the Rust ones take a
tagged `RuntimeValue`; the C receiver-type test is therefore
`rt_core_array_ptr(array)` rather than Rust's `as_typed_ptr!` heap-type check.
Behaviour is matched (non-array → NIL for `filter`/`find`, 0 for
`any`/`all`/both `_truthy` forms). The pre-existing `call_runtime_void` residual
— every parameter declared as `runtime_int_type()` regardless of the real
signature — is unchanged and still open.

`rt_map` is deliberately NOT added to the C runtime: that runtime has no
`rt_option_map` either, so the type-blind `map` path could never link against it
and still cannot. That stays a LOUD link failure rather than a fabricated
half-implementation. `rt_index_of` is likewise still absent from the C runtime —
a wider parity gap on the same axis, recorded here, not addressed.

**Superseded 2026-08-02** — the C-runtime paragraph above no longer holds. See
"The four residual defects" below: `rt_option_map` / `rt_map` / `rt_index_of` /
`rt_array_index_of` / `rt_find` are now defined in the C runtime, because every
primitive they need was already there and every emitter was shown to pass its
operands faithfully. The `rt_par_*` family is still deliberately absent.

## The four residual defects (2026-08-02, follow-up lane) — ALL FIXED

Four defects were carried as "recorded, not resolved" by the lanes above. All
four are closed here. The governing rule was applied first, per symbol: **an
unresolved symbol is not automatically a missing implementation**, so nothing
was implemented until its emitters were shown to pass `receiver + args`
verbatim.

### Emitter-operand verification, per symbol (the gate)

Re-verified this lane by reading the emission code, not inherited:

| symbol | dispatch sites | emitted call | operands faithful? | verdict |
|---|---|---|---|---|
| `rt_find` | `instr/calls.rs`, `instr/closures_structs.rs`, `llvm/emitter.rs`, `llvm/functions.rs` (type-blind) | `(receiver, arg)` | yes — `llvm/emitter.rs:1452` builds `rt_args = [recv] + args` via `self.get()`; `functions.rs` builds `all_args_vregs` the same way; Cranelift uses `get_vreg_or_default` over `args` with the receiver already in slot 0 | implement |
| `rt_reverse` | same four | `(receiver)` | yes | remap (already existed) |
| `rt_map` | `llvm/functions.rs` (type-blind) — the one site the previous lane missed | `(receiver, closure)` | yes | remap + implement in C |
| `rt_index_of` / `rt_array_index_of` | `instr/calls.rs`, `llvm/emitter.rs`, `llvm/functions.rs` | `(haystack, needle)` | yes | implement in C |
| `rt_option_map` | reached only via `rt_map` | `(value, closure)` | yes | implement in C |
| `rt_par_map` / `rt_par_filter` / `rt_par_for_each` | `llvm/emitter.rs` | passes **2**, `runtime_sffi.rs` declares **4** (`input_len`, `backend` DROPPED) | **NO** | **still loud, deliberately** |
| `rt_par_reduce` | `llvm/emitter.rs` | passes **3**, declares **5** | **NO** | **still loud, deliberately** |

The `rt_par_*` verdict was re-checked, not inherited: they remain undefined in
both runtimes and the arity check added to `call_runtime_void` (defect 4)
deliberately **fails closed** on them so the operand drop cannot be papered
over by a correct-looking declaration.

### 1. Array `.find()` was UNREACHABLE — fixed without touching text (PROVED)

`codegen/instr/calls.rs` **and** the type-blind table in
`codegen/llvm/functions.rs` each held TWO `"find"` arms in one `match`:
`"find" | "find_str" => rt_string_find` and, further down,
`"find" => rt_array_find`. Rust `match` is first-match-wins, so the array arm
was dead. `instr/closures_structs.rs` and `llvm/emitter.rs` had no array arm at
all. Every `arr.find(pred)` on a type-blind path therefore answered the `-1`
receiver-mismatch sentinel of the text helper — match at index 0 included —
while the type-AWARE LLVM table answered with the element. Same source, two
answers per backend, no error, exit 0.

**How the return-shape objection was resolved rather than dodged.** The reason
the previous lane stopped here is real: array `find` returns the ELEMENT (a
tagged `RuntimeValue`), text `find` returns an INDEX (a raw `i64`). The
resolution is that the dual shape is **already the contract**, not something a
polymorphic symbol would introduce:

- `hir/lower/expr/mod.rs:1071` gates its whole result-type table on
  `if is_string`, and `find | index_of | find_str | rfind | last_index_of =>
  TypeId::I64` lives INSIDE that gate;
- the array arm (`if is_array`, same file) has **no `find` entry at all**, so an
  array `find` is not typed `I64` and no consumer decodes it as a raw index;
- every Cranelift runtime call is declared `i64 -> i64` regardless
  (`instr/calls.rs` signature builder), so the machine word is the same either
  way — only the consumer's interpretation differs, and that interpretation is
  already receiver-derived.

So `rt_find(receiver, arg) -> i64` dispatches on **receiver AND argument**:

| receiver | argument | route | before | after |
|---|---|---|---|---|
| array | callable closure | `rt_array_find` | `-1` always | the matching element / nil |
| array | anything else | `rt_string_find` | `-1` | `-1` (unchanged) |
| text | text | `rt_string_find` | raw index | raw index (**bit-for-bit unchanged**) |
| anything else | — | `rt_string_find` | `-1` | `-1` (unchanged) |

Requiring a callable closure for the array branch is what keeps "without
changing text semantics" a provable statement instead of a hope: **the only
input class whose answer changes is the one that was unconditionally wrong.**
`find_str` is text-only in the interpreter (`interpreter_method/string.rs`
`"find_str" | "find" | "index_of"`) and keeps its direct route. The type-AWARE
LLVM table is untouched — it was already right and is more precise.

### 2. `reverse` → `rt_array_reverse` for EVERY receiver — fixed (PROVED)

`rt_array_reverse` reverses **in place** and returns a **bool**. All four
type-blind tables applied it to every receiver. Disposition per receiver, with
semantics pinned to the interpreter, not guessed:

| receiver | interpreter (the spec) | before | after |
|---|---|---|---|
| array | `interpreter_method/collections.rs:169` `"rev" \| "reverse"` → `Value::array(new_arr)`: copies, reverses the COPY, receiver untouched | receiver MUTATED, expression value was the receiver (via the `in_place` list) | new array, receiver untouched |
| text | `interpreter_method/string.rs:357` `"rev" \| "reverse"` → new text | `false` (bool receiver-mismatch answer) | new reversed text |
| tuple | `interpreter_method/collections.rs:768` → new tuple | `false` | loud refusal (`rt_reverse` refuses a non-array/non-text receiver) — a wrong answer becomes an error, never the reverse |
| anything else | error | `false` | loud refusal |

`rt_reverse` already existed in **both** runtimes with exactly the right
behaviour and was carrying a stale comment saying the `reverse` mapping was
"deliberately left alone"; both comments are corrected. On the C lane this is
strictly a repair in two directions at once: `rt_array_reverse` has **never**
been defined in `src/runtime/*.c`, so `arr.reverse()` did not even link there.

The type-AWARE LLVM arm `("Array","reverse")` moves to `rt_array_reversed` (the
copying twin) for the same reason.

**The trap this fix could have fallen into, and did not:** `functions.rs` kept
an `in_place` set — `push | clear | reverse | sort` — whose members return the
RECEIVER as the expression value. Leaving `reverse` in it would have discarded
the new array and yielded the unmodified receiver, converting the fix into a
silent wrong answer. `reverse` is removed from that set. `sort` is left in it
deliberately: it still lowers to the in-place `rt_array_sort`, so it carries the
identical divergence from the interpreter (which copies) — **recorded here as
the enumerated sibling, not silently changed**, because closing it needs a
copying runtime symbol that does not yet exist.

### 3. C-runtime parity — implemented, with the reason it is not a fabrication

**Decision: implement.** The previous lane's "keep it loud" was correct at the
time and is wrong now, and the difference is verifiable rather than a matter of
taste. "Keep loud" is right when a receiver would have to invent behaviour. Here
nothing had to be invented: **every primitive already existed in
`runtime_native.c`** — `rt_array_map` (5954), `rt_array_find` (6075),
`rt_closure_func_ptr` (5924), `rt_string_find` (3227), `rt_is_none` (3517),
`rt_enum_payload` (5827), `rt_enum_new` (5780), `rt_native_eq` (2972) — and
`rt_array_at` in that same file already builds its Option with
`rt_enum_new(1, 0, x)` for Some and `rt_enum_new(1, 1, nil)` for None, so even
the Option encoding is the file's own, not imported from the Rust twin.

Five symbols added: `rt_find`, `rt_index_of`, `rt_array_index_of`,
`rt_option_map`, `rt_map`. `rt_array_index_of` already had a `runtime_sffi.rs`
spec and a Rust definition, so its absence here was a plain parity hole.

**Signature divergence recorded, not reconciled:** the C entry points take a raw
`int64_t` or an `SplArray*` where Rust takes a tagged `RuntimeValue`; the
receiver test is `rt_core_array_ptr` against Rust's `as_typed_ptr!` heap-type
check; value equality is `rt_native_eq` here against Rust's `rt_value_eq`.
Behaviour is matched, the C types are not. This is the same treatment §6 gives
`rt_value_float` (Rust `f64` vs C raw-bits `int64_t`), which remains open.

**Still deliberately loud in C:** `rt_par_map`, `rt_par_filter`,
`rt_par_for_each`, `rt_par_reduce` — their emitters drop operands.

### 4. `call_runtime_void` declared every parameter `runtime_int_type()` — fixed

`codegen/llvm/emitter.rs` auto-declared `void(i64, …)` for every symbol,
regardless of the real signature, so `rt_decision_probe(u64, bool)` was declared
`void(i64, i64)` and `rt_condition_probe(u64, u32, bool)` was declared
`void(i64, i64, i64)`. It survived only because the low bits land correctly on
the SysV and AArch64 ABIs — the declaration was simply never required to agree
with the runtime.

It now reads `runtime_sffi::spec_for(name)` (new lookup) and declares the real
slot widths, narrowing or widening each argument to its slot. Three cases are
deliberately NOT "fixed", because fixing them would hide a defect:

- **no spec at all** (`rt_contract_check`, `rt_unit_bound_check`,
  `rt_generator_yield` — defined in neither runtime) → keeps the blind i64 shape
  and stays loud; inventing a signature would dress up a symbol that must fail;
- **spec arity disagrees with the call** (`rt_par_for_each`: 2 passed against 4
  declared) → the arity check **fails closed**, so the operand drop stays
  visible;
- **`F64` slots** → not mapped, because `rt_value_float` is `f64` in Rust and
  raw-bits `int64_t` in C (§6) and silently picking one would be exactly the
  guess this change removes.

A non-void spec return is now honoured too: `rt_actor_reply` is
`(RuntimeValue) -> RuntimeValue` and was being declared `void`, leaving two
disagreeing declarations of one symbol in play. The result is discarded at the
call site, which is what the caller wanted all along.

### 5. Enumerated sibling found and fixed — the last `rt_option_map` misroute

Enumerating the family (rather than fixing the reported site) turned up that the
type-blind table in `codegen/llvm/functions.rs` was **still** routing the bare
name `map` to `rt_option_map` after the sibling arms in `llvm/emitter.rs` and
`instr/closures_structs.rs` had been corrected. Same defect, same silent shape:
one closure call, on the NIL that `rt_enum_payload` returns for a non-enum,
Some-wrapped, exit 0. Now `rt_map`.

### Link-level evidence (codegen proves nothing)

Established against BUILT objects, never `nm -u` (blind to weak zero-size
definitions). Base object compiled from the origin-tip `runtime_native.c` at
`e4b4561c803`, new object from the same file with these changes, everything else
identical — the supporting objects are the exact set
`scripts/check/build-core-c-bootstrap-runtime-capsule.shs` lists, so the link is
the repo's own capsule shape and not a hand-picked one.

| link (`ld.lld`) | result |
|---|---|
| probe vs **BASE** object | `rc=1`; exactly `rt_find`, `rt_index_of`, `rt_array_index_of`, `rt_map`, `rt_option_map` undefined; **no artifact on disk** |
| probe vs **NEW** object | `rc=0`; `file` → `ELF 64-bit LSB pie executable, x86-64`; `nm --defined-only` shows all five at real addresses plus `rt_reverse`; and it RUNS |

**33 of 33 printed values match hand-computed expectations** — array find
element and predicate call count, empty-receiver nil, text find hit/miss/empty
needle, array-with-text-argument keeping its old `-1`, index_of at 0 / middle /
absent / on text, map length + per-element values + call count, Option
`Some(5) → Some(10)` in one call, `None` passed through in zero calls, and
reverse's copy plus the receiver being unmutated.

**Value-level comparison earned its keep again — the failure was MINE.** The
first run showed `array find element = 0, predicate calls = 3`. The
implementation was right; the probe's predicate returned a **raw** `1` instead
of a tagged value, so `rt_core_value_truthy` read tag bits `001` (not `TAG_INT`)
and every element read falsy. A cross-engine comparison would have scored this
PASS or blamed the runtime. It is pinned in the probe by a true-positive control
that calls the pre-existing, untouched `rt_array_find` directly and must agree
value-for-value.

**Non-vacuity PROVED by sabotaging the IMPLEMENTATION, not a shim:** the array
branches of `rt_find` and `rt_map` and the comparison inside
`rt_array_index_of` were reverted in the C source with the probe untouched →
**11 checks RED**, reproducing the original defect signatures exactly (map
closure call count `1` instead of `3`; find predicate count `0`; every index_of
`-1`). The `rt_array_find` control and all text checks stayed GREEN, proving the
sabotage hit the new dispatch and not a shared helper.

### Regression guards added

- `runtime/src/value/collection_tests.rs` — `rt_find` receiver dispatch
  (element + call count + text bit-for-bit equality with `rt_string_find`) and
  `rt_reverse` copying with the receiver asserted UNMUTATED.
- `codegen/llvm/emitter.rs` — bare-name table routes the polymorphic methods to
  polymorphic helpers, paired with a true-positive control that
  receiver-SPECIFIC methods stay specific; plus a guard on the SFFI specs
  `call_runtime_void` now depends on, including that `rt_par_for_each` still
  declares 4 params so the fail-closed arity check keeps meaning something.
- `codegen/instr/closures_structs.rs` — source-region scan of both Cranelift
  bare-name tables asserting the dead `find`/`reverse` arms are gone AND the
  live ones present, so deleting an arm cannot satisfy it. The scan skips each
  file's own `mod tests` region so it cannot match its own text.

### Test results and pre-existing failures, proved at the SAME base sha

Base sha `e4b4561c803f07e3f7cc7a5882876bd78ab6e3c2`, taken from `git ls-remote`.

- `cargo test -p simple-runtime --release --lib` → **1084 passed / 7 failed**.
  That is the documented `1082 / 7` plus exactly the 2 tests added here, both
  passing. The 7 failures are the same by name (`executor::` ×2, `loader::` ×2,
  `value::collections::tests::test_dict_invalid_value`,
  `value::collections::tests::test_low_heap_tagged_values_do_not_crash_collection_runtime`,
  `value::heap::attr_tests::owner_attribution_orders_by_live_bytes_and_frees_settle`)
  — none on any path this change touches.
- `cargo test -p simple-compiler --features llvm --release --lib codegen:: --
  --test-threads=1` → the failure **NAME SETS are IDENTICAL** with these
  changes present and with the five compiler files reverted to their base-sha
  content and rebuilt: `codegen::common_backend::tests::referenced_empty_extern_is_declared`
  and `codegen::llvm::functions::tests::rt_value_bool_calls_receive_raw_boolean_bits`,
  diffed with `diff`, no delta.
- The suite also **SIGSEGVs at `codegen::local_execution_tests::llvm_jit_tests::
  test_llvm_jit_basic`** on BOTH builds, at the same test, so it is PROVED
  pre-existing and is not absorbed into this result. It also reproduces when
  that test is run alone, so it is not a test-ordering artifact. It is
  unrelated to these tables (it JITs and runs basic arithmetic) and remains
  open, recorded here rather than left implicit.

  **ROOT-CAUSED AND FIXED 2026-08-02.** It is a use-after-free at **drop**
  time, not in the code under test — `assert_eq!(result, 42)` had already
  passed. Faulting PC `llvm::LLVMContext::removeModule+11`, reached via:

  ```text
  LocalExecutionManager::drop -> LlvmJitCompiler::drop
    -> ExecutionEngine::drop -> MCJIT::~MCJIT
    -> OwningModuleContainer::~OwningModuleContainer -> Module::~Module
    -> LLVMContext::removeModule            (SIGSEGV)
  ```

  `LlvmJitCompiler::compile_module` built the module inside a **local**
  `LlvmBackend`, whose `Box<Context>` owns the `LLVMContext`, then handed the
  module to `create_jit_execution_engine`. **MCJIT takes ownership of the
  module.** The backend then went out of scope at the end of `compile_module`
  and freed the context, so dropping the engine later ran `~Module` against
  freed memory. The struct's own `context` field was a red herring: it is never
  the context the JIT module lives in, and its field ordering was already
  correct — which is why the existing "borrowing fields declared first" comment
  looked like it had already covered this.

  Fixed by storing the backend beside the engine it feeds, declared **after**
  `execution_engine` so the engine is destroyed while the context is still
  valid, and retiring a previous engine before its backend is replaced.
  PROVED: 3/3 `llvm_jit_tests` green after the change; the same binary
  segfaulted at `test_llvm_jit_basic` before it. Nothing skipped or disabled.

**Guard non-vacuity PROVED by sabotaging the IMPLEMENTATION, not a shim.** Four
mappings were reverted in the non-test source with every test body untouched —
`closures_structs.rs` `find` back to `rt_string_find`, `calls.rs` `find` back to
the dead `rt_array_find`, `emitter.rs` `reverse` back to `rt_array_reverse`, and
the `rt_decision_probe` spec back to `[I64, I64]` — and **all three codegen
guards went RED**. Restoring turned them GREEN. Separately, reverting `rt_find`'s
array branch in the Rust runtime turned `rt_find_dispatches_on_receiver_without_changing_text`
RED on the exact assertion "array find must return the matching ELEMENT", while
`rt_reverse_copies_and_leaves_the_receiver_alone` stayed GREEN — so the two
tests are independent and neither is carrying the other.

### What is still open (recorded, not silently closed)

- **`sort` has the same divergence `reverse` had**: it lowers to the in-place
  `rt_array_sort` and stays in the `in_place` set, while the interpreter's array
  `"sort"` copies. Needs a copying runtime symbol first.

  **CLOSED 2026-08-02 — but the predicted fix was WRONG, and finding out why
  matters more than the fix.** "The interpreter's array `sort` copies" is what
  `interpreter_method/collections.rs` says in isolation, and it is **not what
  the language does**. `interpreter_method/mod.rs` lists `"sort"` in
  `MUTATING_METHODS` and **writes the result back to the receiver binding**.
  Measured end to end on the interpreter — the spec:

  ```text
  var a = [3, 1, 2]
  val b = a.sort()     # b = [1, 2, 3]  AND  a = [1, 2, 3]
  "cba".sort()         # error: method `sort` not found on type `str`  (rc=1)
  ```

  A *copying* `sort` — the obvious "make it like `reverse`" change — was
  written, measured against that hand-computed expectation, **caught diverging
  on the aliasing axis, and replaced.** Cross-engine agreement would not have
  caught it; only comparing against the interpreter's observed behaviour did.

  What was actually wrong with `"sort" => rt_array_sort`:
  - `rt_array_sort` returns a **bool**, so the value was only ever right while
    `sort` sat in the `in_place` set that substitutes the receiver vreg;
  - on a **text** receiver it returned `false` and that substitution silently
    handed back the unsorted receiver, where the interpreter errors outright;
  - `runtime_native.c` has **never defined `rt_array_sort`**, so `arr.sort()`
    did not link at all on the native lane.

  Fixed by adding **`rt_sort` to both runtimes** — sort an array in place,
  return that same array, refuse any other receiver loudly (`exit 70`) rather
  than substitute a value — routing the four type-blind tables and the
  type-aware LLVM arm to it, and **removing `sort` from the `in_place` set**,
  because `rt_sort` now supplies its own return value and the substitution
  would otherwise defeat the text refusal.

  PROVED, both engines, `[jit-fallback]` asserted 0:

  | case  | JIT                  | interpreter          |
  |-------|----------------------|----------------------|
  | array | `b=[1,2,3] a=[1,2,3]`| `b=[1,2,3] a=[1,2,3]`|
  | text  | rc=70, refusal       | rc=1, refusal        |

  Before the fix the JIT printed `u=abc` for `"cba".sort()` — a silent wrong
  answer. `simple-compiler --lib` 3456/118 and `simple-runtime --lib` 1085/7,
  failure NAME SETS identical to baseline by `diff`.
  `runtime_sffi::all_funcs_have_unique_names` was confirmed **pre-existing** by
  removing the new spec line and re-running (1178/1179 duplicate either way).

- **OPEN — `reverse` now diverges on receiver rebinding, introduced by
  `982ed57f65e`.** The same `MUTATING_METHODS` write-back that governs `sort`
  also lists `"reverse"`, so the interpreter rebinds the receiver there too.
  Routing `reverse` to the copying `rt_reverse` fixed the text case and the
  native link but made the JIT stop rebinding. Measured on a binary built at
  `14d7aba` (which contains that commit):

  ```text
  val a = [3, 1, 2]; val b = a.reverse()
  JIT          b=[2,1,3]  a=[3,1,2]      <-- receiver NOT rebound
  interpreter  b=[2,1,3]  a=[2,1,3]      <-- receiver rebound
  ```

  A binary predating the commit agreed with the interpreter on both. So this is
  a **live silent wrong answer on the aliasing axis**, of exactly the shape the
  `reverse` fix was written to remove.

  **CLOSED 2026-08-02 for ARRAY receivers — and the predicted resolution was
  again wrong.** The guess above ("the one `sort` took") assumed `reverse` and
  `rev`/`reversed` are one method. They are not, and that is the whole defect:
  `interpreter_method/mod.rs` lists `"reverse"` in `MUTATING_METHODS` and
  **deliberately omits `"rev"` and `"reversed"`**, so the interpreter rebinds
  the receiver for `reverse` alone. Both spellings share ONE arm in
  `interpreter_method/collections.rs` — the single-layer read that produced the
  wrong prediction for `sort` produced a wrong one here too. Measured:

  ```text
  var a = [1, 2, 3]
  a.reverse()   ->  [3,2,1]  AND  a == [3,2,1]     mutating spelling
  a.rev()       ->  [3,2,1]  AND  a == [1,2,3]     pure spelling
  ```

  Fixed by **splitting the symbols**, not by changing `rt_reverse`: new
  `rt_reverse_mut` in both runtimes (reverse the array in place, return that
  same array) serves `reverse`; `rt_reverse` keeps serving `rev`/`reversed`.
  The type-aware LLVM arm `("Array","reverse")` had a second, independent
  defect — `rt_array_reversed` has **never existed in `runtime_native.c`**, so
  that arm did not link on the native lane at all — closed by the same routing.

  **Verdict on the landed test `rt_reverse_copies_and_leaves_the_receiver_alone`:
  it pinned CORRECT semantics on a FALSE premise.** Every assertion in it is
  right — they describe `rt_reverse`, the `rev`/`reversed` helper — so all of
  them are kept. Only its opening sentence, that `rt_reverse` "is what the
  `reverse` METHOD now lowers to", was false, and that sentence is corrected in
  place. By contrast the three **codegen guard assertions** demanding
  `"reverse" => rt_reverse` genuinely **pinned the bug** and were replaced, with
  negative assertions added plus a new true-positive control that
  `rev`/`reversed` must not follow `reverse`. Nothing was weakened or deleted.

  Non-vacuity: after the fix `rev` still leaves `a == [1,2,3]` while `reverse`
  now leaves `a == [3,2,1]`. The two spellings moved apart, which no blanket
  semantics change could produce.

### Mutating-method family sweep (2026-08-02)

All 33 names in `interpreter_method/mod.rs`'s `MUTATING_METHODS` were checked
against the five codegen dispatch tables. Only **8** have any codegen route;
the other 25 (`push_front`, `insert`, `extend`, `dedup`, `retain`, `swap`,
`rotate_*`, `truncate`, `drain`, `merge`, …) have **no lowering at all** and are
out of scope here. Per-symbol verdict, measured on both engines with
`jit-fallback` asserted 0:

| method | route | JIT vs interp | verdict |
|---|---|---|---|
| `reverse` (array) | `rt_reverse_mut` | agree after fix | **FIXED here** |
| `rev` / `reversed` | `rt_reverse` | agree | correct, left alone |
| `sort` | `rt_sort` | agree | fixed earlier |
| `push` | `rt_array_push` | agree | correct, left alone |
| `pop` | `rt_array_pop` | agree | correct, left alone |
| `append` | `rt_array_push` | agree | correct, left alone |
| `clear` | `rt_array_clear` | agree | correct, left alone |
| `set` | `rt_dict_set` / `rt_index_set` / `rt_tuple_set` | not measured | **untested**, left alone |

- **OPEN — TEXT receivers diverge for all four string mutators.** Deliberately
  not fixed with `reverse`, because it is one design question spanning four
  methods, not a `reverse` bug. Measured `var t = "abc"`:

  ```text
  method    JIT expr/recv        interp expr/recv
  push      0 / abc              abcd / abcd
  pop       nil / abc            Option::Some(c) / abc
  clear     abc / abc            (empty) / (empty)
  reverse   cba / abc            cba / cba
  ```

  The interpreter rebinds a `Str` receiver because the write-back rule is
  `MUTATING_METHODS.contains(method) && discriminant(result)==discriminant(recv)`
  and `Str == Str` passes — even though the same file documents that "strings in
  Simple are value types with NO mutating methods". So the interpreter
  contradicts its own stated rule, and the JIT answers garbage (`0`, `nil`) from
  array helpers applied to text. **Both sides are wrong here**, in different
  ways, which is why this needs a decision rather than a patch. Text behaviour
  was left byte-for-byte unchanged by the `reverse` fix.
- **OPEN — the LLVM emitter table has no `rev`/`reversed` arm at all**, unlike
  the two Cranelift tables. Not filled in, because this lane has no measurement
  of the LLVM path for those spellings and adding an unverified route is the
  same class of mistake being undone here.
- **`rt_value_float` signature divergence** (§6) — unchanged.
- **`rt_par_*`** — must stay undefined until their emitters thread the real
  operands.
- **`x in <range>` engine divergence** — unchanged, still a language decision.

### Pre-existing failures, proved at the same base sha

- duplicate `rt_dir_exists` spec in `codegen/runtime_sffi.rs` failing
  `all_funcs_have_unique_names` — present with these changes absent;
- `simple-runtime --lib` at `1080 passed / 7 failed` before `f835ee71522`,
  `1082 passed / 7 failed` after (that commit added 2 tests); the same 7
  failures by name.
