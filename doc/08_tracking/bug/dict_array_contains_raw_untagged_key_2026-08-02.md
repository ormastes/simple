# `.has()` / `.contains()` / `in` answer membership questions with an untagged key

- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  LLVM backend `bare_rt_redirect`, see "The emitter, LOCATED"), codegen fix
  specified but NOT landed (no host pipeline can verify it; see "Reproduction
  gap")
- **Found:** 2026-08-02, follow-up to the `--source`-less `native-build` hang
  recorded in `stage3_selfhost_tuple_positional_field_segv_2026-08-02.md`
- **Severity:** high — a silent wrong answer in BOTH directions on a core
  container operation, live on the self-hosted compiler at origin tip
- **Component:** dict/array membership lowering (the `rt_contains` call
  boundary), `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
  region and whatever emits `rt_contains`
- **Verified live at:** origin `1a6c1e362a5076736a15a7c72d7c376d80279fb6`

## Symptom (PROVED)

Stage-3 compiler built from tip (`727 compiled, 0 cached, 0 failed`,
127,684,656 B, `strings | grep -c "enum construction: unregistered enum"` = **2**,
`--version` = `simple-bootstrap 1.0.0-beta`). Probe compiled by that binary,
every expectation hand-computed:

| probe | expected | measured |
|---|---|---|
| `b.has(7) has(9) has(11) has(13)` on a dict holding all four | `true true true true` | **`true false true true`** |
| `b[7] b[9] b[11] b[13]` (index read, same dict) | `70 90 110 130` | `70 90 110 130` ✓ |
| `b.keys().len()` | `4` | `4` ✓ |
| `b.has(5) b.has(6)` (absent) | `false false` | `false false` ✓ |
| `[10,9,30].contains(10/9/30/7)` | `true true true false` | **`false false false false`** |
| `9 in b` / `5 in b` (5 is ABSENT) | `true false` | **`true true`** |
| 64-key dict `v[i]=i`, count present-but-not-found | `0 of 64` | **`8 of 64`** (`keys()` = 64 ✓) |

The identical table is produced by the previous admitted Stage-2 binary, so this
is **not** a stale-binary artifact — it reproduces on a compiler built from the
current tip.

Note both directions: `[10,9,30].contains(10)` is a false NEGATIVE, `5 in b` is
a false POSITIVE. The dict itself is intact — index reads and `keys()` are
correct — so only the membership query is wrong.

## Root cause (PROVED by disassembly)

The store side tags the key; the membership query does not. From the
tip-compiled probe, same four keys, same dict:

| key | `rt_dict_set` (store) | `rt_contains` (query) |
|---|---|---|
| 7 | `mov $0x38,%esi` = 56 = `7<<3` | `mov $0x7,%esi` = 7 |
| 9 | `mov $0x48,%esi` = 72 = `9<<3` | `mov $0x9,%esi` = 9 |
| 11 | `mov $0x58,%esi` = 88 = `11<<3` | `mov $0xb,%esi` = 11 |
| 13 | `mov $0x68,%esi` = 104 = `13<<3` | `mov $0xd,%esi` = 13 |

`rt_contains(collection, value)` requires a TAGGED value on both the C runtime
path (`runtime_native.c:3479`, which forwards a dict to `rt_core_dict_has` and
scans an array with `rt_native_eq`) and the pure-Simple path
(`simple_core/core_string.spl:600`). `rt_core_dict_has` canonicalises through
`rt_core_dict_canon_key` (`runtime_native.c:6388`), which reads the low 3 bits
as a type tag (`RT_VALUE_TAG_INT 0`, `HEAP 1`, `FLOAT 2`, `SPECIAL 3`). A raw
untagged integer therefore canonicalises as some unrelated value and is compared
against correctly-tagged stored keys.

The C runtime is NOT at fault: `rt_core_dict_has` and `rt_core_dict_lookup` are
line-for-line identical in their probe logic, and the index read (which passes
`$0x48`, tagged) returns the right value through the same table.

The index read path lowers its key with `lower_dict_key`
(`method_calls_literals.spl`), which is `box_runtime_value(lower_expr(key))` —
i.e. it tags. The membership path does not go through it.

The Rust seed does not have this bug and says so in a comment:
`src/compiler_rust/compiler/src/codegen/common_backend.rs:608` —
"methods.rs `wrap_value` before calling rt_contains". The self-hosted path omits
the equivalent wrap.

## Why the wrong answers look random

Whether a mismatched key accidentally collides with some other stored key
depends on the dict's contents and capacity, so the answer is uncorrelated with
membership rather than uniformly wrong. Two over-fitted rules were tried and
**refuted by measurement**, and are recorded so nobody re-derives them:

- "missing keys are exactly `k ≡ 1 (mod 8)`" — fits a 130-key dict exactly
  (missing 1,9,17,…,129) but is refuted by a 2-key dict where keys 8 and 9 both
  fail, and by a 64-key dict where 8 of 64 fail.
- "it depends on operand provenance (literal/`val` = raw, array element =
  tagged)" — refuted: a dict holding 8 and 9 answers `false` for all three
  operand forms, while a separate 3-block probe answered correctly for keys read
  out of an array.

Only the ABI mismatch above is established. Any deterministic rule is NOT.

## Relationship to the `--source`-less `native-build` hang — INFERRED, not proved

`LoopDetector.reachable_from` (`src/compiler/60.mir_opt/mir_opt/loop_detect.spl:155`)
drives its worklist with `visited.has(cur.id)` and `succ_map[cur.id] ?? []`. If
`has` reports a visited block as unvisited, successors are re-pushed forever and
both the stack and `visited` grow without bound — which matches the observed
profile exactly (5.2 GB at 110 s, 10 GB at ~220 s, unbounded, with `opt-18`,
`llc-18` and `clang-18` each having already run exactly once, so it is not a
subprocess storm).

This is **INFERRED**. A standalone replica of `reachable_from` on a 3-block CFG
with a 1↔2 cycle **terminated correctly** (3 iterations, 2 visited, empty stack —
all hand-computed), so the replica does not demonstrate the chain. Confirming it
requires observing `visited.has` returning false for a visited block inside the
real compiler run, which this lane did not do.

## Why no fix was proposed originally

The fix is "tag the value operand before `rt_contains`, as `lower_dict_key`
already does for the index path". The blocker was that **the emitter was not
located**. The pure-Simple compiler contains exactly one contains-related
runtime symbol emission — `MirConstValue.Str("rt_dict_contains")` at
`method_calls_literals.spl:1282`, correctly tagged via `lower_dict_key` and gated
on `receiver_is_dict` — and the string `rt_contains` does not appear anywhere in
`src/compiler/**/*.spl` or `src/compiler/70.backend/**`. Yet the emitted binary
calls `rt_contains`.

## The emitter, LOCATED (2026-08-02 follow-up lane) — PROVED

`rt_contains` is absent from `src/compiler/**` because **it is not emitted by
pure-Simple code at all**. The pure-Simple self-hosted compiler links in and
uses the *Rust seed's* LLVM backend for native-build IR emission, and that
backend owns the mapping.

Proof that the Rust LLVM backend is inside the pure-Simple binary (positive
capability probe, not a size heuristic): the string
`missing receiver for runtime redirect` occurs in exactly ONE place in the whole
tree — `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:1972`,
inside the `bare_rt_redirect` block — and `strings -a` finds it in **every**
pure-Simple stage binary checked (`bin/release/x86_64-unknown-linux-gnu/
simple.bootstrap-main-stage-2026-08-01.bak`,
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`,
`build/bootstrap/release_beta_verify/stage2/x86_64-unknown-linux-gnu/simple`),
all three of which carry `enum construction: unregistered enum` = 2 and no
`bootstrap seed only` banner, i.e. they are genuinely pure-Simple builds.

Inside that block, `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs`
carries **two independent defects**, either of which produces a wrong answer in
both directions:

1. **Untagged key (the ABI mismatch this bug reports).** The table at ~:1928
   maps `"contains" => Some("rt_contains")`, and the argument loop at ~:1980
   passes every argument through `coerce_value_to_type(val, i64)` only — there is
   **no** tag-box. The Cranelift path does the opposite and documents exactly this
   failure: `codegen/instr/methods.rs:339-357` calls `wrap_value(...)` with the
   comment *"Box the search value so an int key/element matches what `get`/`set`
   stored — a raw i64 would hash/compare as a bogus tagged value and
   `Dict<i64,_>.has(k)` would always miss"*, and
   `codegen/instr/closures_structs.rs:1717` sets
   `box_dict_key = matches!(runtime_func, "rt_index_get" | "rt_dict_remove" | "rt_contains")`.
   The LLVM `qualified_rt_redirect` sibling at ~:2178 has the same omission.
   This reproduces the disassembly in the table above exactly: a bare MIR
   `Call { target: "contains" }` (which is what the pure-Simple lowering emits
   when it fails to classify the receiver) becomes `mov $0x7,%esi; call rt_contains`.

2. **`int8_t` return read as `i64`.** In the same block the `returns_bool`
   list at ~:1987 is
   `"rt_array_push" | "rt_array_clear" | "rt_array_reverse" | "rt_array_sort" | "rt_index_set"`
   — it **omits `rt_contains`**, so the callee is declared to return `i64`. Family
   check against `src/runtime/runtime.h`: of every target in `bare_rt_redirect`,
   the `int8_t`-returning ones are exactly `rt_contains`, `rt_array_push`,
   `rt_array_clear`, `rt_index_set`; `rt_contains` is the **only** member of that
   family missing from the list. Under SysV x86-64 an `int8_t` result leaves the
   upper 56 bits of `%rax` undefined, so the truthiness test reads garbage. That
   this is an oversight and not intent is settled by the sibling
   `qualified_rt_redirect` block 200 lines below (~:2186), whose otherwise
   identical `returns_bool` list DOES include `"rt_contains"`.

### REFUTED hypotheses (recorded so nobody re-derives them)

- **"Name resolution against compiled-in `simple_core` exports"** (the previous
  lane's leading suspect, and the `rt_prefix_local_function_collision` link) —
  **REFUTED**. `rt_contains` exists in Simple only as a *definition*
  (`src/runtime/simple_core/core_string.spl:600`) and in C
  (`runtime_native.c:3479`); `nm` on a pure-Simple stage binary shows it as
  `T rt_contains`, a linked runtime definition, never an emitter-table entry.
  No pure-Simple path constructs the name, and no `"rt_" +` concatenation exists
  anywhere under `src/compiler/`.
- **"The Rust seed does not have this bug"** (asserted in the Root cause section
  above from the `common_backend.rs:608` comment) — **REFUTED for the LLVM
  backend**. That comment describes the Cranelift path only. The seed's LLVM
  backend is the emitter.

### Negative results from this lane — where the bug is NOT

All seven probe rows were re-run and every one is **CORRECT** on:
- the seed interpreter (`simple p1.spl`),
- the seed JIT (`SIMPLE_EXECUTION_MODE=native`),
- the Rust `native-build` LLVM path
  (`SIMPLE_NATIVE_BUILD_RUST=1 simple native-build --source . --entry p1.spl`),
  including a 64-key dict (0 of 64 missing), a 130-key dict (0 of 130 missing)
  and a 2-key dict holding 8 and 9.

Those shapes take the typed `BuiltinMethod` path (`methods.rs`), which boxes
correctly, so they never reach `bare_rt_redirect`. Only a MIR-emitted bare
`Call { target: "contains" }` does — which is why the defect is exclusive to the
pure-Simple lowering feeding the Rust LLVM backend.

### Reproduction gap — why the codegen patch is still NOT landed

No compiler on this host can drive the affected pipeline end to end:
`simple.bootstrap-main-stage-2026-08-01.bak` reaches MIR (it prints
`[mir-lower] WARNING: unresolved method call 'has' lowered to const-0
placeholder` for a plain `var b: {i64: i64}` receiver — see below) and then
SIGILLs; `build/bootstrap/stage2/.../simple` fails with
`AOT compile error in p1: <invalid-heap:...>`;
`build/bootstrap/release_beta_verify/stage2/.../simple` exits 0 with
`[WARN] no mode matched, falling through` and emits nothing. Rebuilding the seed
to verify a codegen change belongs to the bootstrap lane. The patch is fully
specified above (add `"rt_contains"` to the `returns_bool` list; `wrap_value`
the search operand in both `bare_rt_redirect` and `qualified_rt_redirect`) and
must NOT be landed unverified — an incorrect box would double-tag an
already-tagged operand and trade one silent wrong answer for another.

### Additional PROVED defect found while probing (separate from the ABI bug)

On the pure-Simple lowering at tip, a plain `var b: {i64: i64} = {}` receiver is
**not classified as a dict**: `receiver_is_dict`
(`method_calls_literals.spl:1160-1190`) is false for it, so `.has`/`.contains`/
`.keys` fall through to `case Unresolved:` instead of the correct
`rt_dict_contains` arm at :1278. Live evidence: eleven
`[mir-lower] WARNING: unresolved method call '<has|keys|contains>' lowered to
const-0 placeholder` lines from
`simple.bootstrap-main-stage-2026-08-01.bak native-build p1.spl`. At tip that
fallback emits `rt_panic` (fails closed), but it is what produces the bare
`Call { target: "contains" }` in builds that predate the panic, and it is the
reason the correct dict arm never fires. Fixing `receiver_is_dict` for this shape
is next step 2 below and is independent of the codegen fix.

## Concrete next steps

1. ~~Find what turns `.has`/`.contains`/`in` into a call to `rt_contains`.~~
   DONE — `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs`
   `bare_rt_redirect` (~:1928/:1980/:1987) and `qualified_rt_redirect` (~:2178).
2. Make `receiver_is_dict` true for a declared `{K: V}` receiver so the existing
   correct `rt_dict_contains` arm at `method_calls_literals.spl:1278` fires
   instead of the unresolved fallback.
3. Arrays: `rt_array_contains` is declared in `llvm_lib_translate.spl:412` but
   never implemented in `runtime_native.c`, and nothing emits a call to it — it
   is a dead declaration and a landmine, not a destination. The correct
   destination for an array `.contains` is the receiver-dispatching
   `rt_contains` (`runtime_native.c:3479` scans the array with `rt_native_eq`),
   which is correct once the needle is tagged — i.e. the same one fix serves
   dict and array. Until that lands, the array path must keep failing LOUDLY
   (the `rt_panic` fallback), never returning a plausible `false`.

## Regression coverage

`test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl` — all seven
rows of the symptom table, each expectation hand-computed. Status on the
deployed seed: **7 total, 7 passed**; sabotaging one expectation
(`expect(b.has(9)).to_equal(false)`) turns it red (`6 passed, 1 failed`), so the
assertions are live. Read the lane-coverage warning in the spec header: like its
sibling `dict_get_miss_returns_nil_spec.spl`, it is green on the interpreter
before and after the codegen fix and is therefore NOT by itself a native-lane
gate — the native lane is gated by building the same cases with `native-build`
and running the ELF.

**Vacuity trap found while writing it:** a bare `assert <expr> == <literal>`
inside an `it` block is silently INERT in this spec DSL — `assert 1 == 2` still
reported `7 passed, 0 failed`. Only `expect(...).to_equal(...)` actually
asserts. Any spec in this tree written with bare `assert` should be treated as
unverified until converted.


## Re-measurement 2026-08-17 (P0-core silent-wrong triage lane) — NOT REPRODUCED

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37 UTC (Rust seed). Probes run under both
`SIMPLE_EXECUTION_MODE=interpreter` and `=jit`.

`d.has(k)` for a key that IS present now returns `true` on both engines:

```
var d: Dict<text, i64> = {}
d.set("k", 1)
print d.has("k")     # -> true, interpreter and JIT
```

No `[mir-lower] WARNING: unresolved method call 'has' lowered to const-0` was
emitted on either run — the doc names that warning as the emitter's signature,
and its absence is the second, independent signal that this path no longer
takes the unresolved arm.

**Scope of this close.** Only the `text`-keyed `.has()` shape on the Rust-seed
interpreter and JIT was measured. The doc also covers `.keys`, `.contains`,
`in`, and array receivers; those were NOT re-measured, so this is not a
whole-doc close. Reduce the doc's scope rather than resolving it outright.
