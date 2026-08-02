# `.has()` / `.contains()` / `in` answer membership questions with an untagged key

- **Status:** OPEN — root cause PROVED, fix NOT attempted (emitter not located; see
  "Why no fix is proposed")
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

## Why no fix is proposed

The fix is "tag the value operand before `rt_contains`, as `lower_dict_key`
already does for the index path". The blocker is that **the emitter was not
located**. The pure-Simple compiler contains exactly one contains-related
runtime symbol emission — `MirConstValue.Str("rt_dict_contains")` at
`method_calls_literals.spl:1282`, correctly tagged via `lower_dict_key` and gated
on `receiver_is_dict` — and the string `rt_contains` does not appear anywhere in
`src/compiler/**/*.spl` or `src/compiler/70.backend/**`. Yet the emitted binary
calls `rt_contains`. Until that path is found, any patch would be a guess.

Concrete next steps for the lane that picks this up:
1. Find what turns `.has`/`.contains`/`in` into a call to the `simple_core`
   `pub fn rt_contains` symbol (name resolution against the compiled-in
   `simple_core` exports is the leading suspect; note the existing
   `codegen_rt_prefix_local_function_collision_sigsegv_2026-07-12` bug in the
   same area).
2. Tag the value operand there with `box_runtime_value`, or make
   `receiver_is_dict` true for these receivers so the existing correct
   `rt_dict_contains` arm at :1278 fires instead.
3. Arrays need their own answer: `rt_array_contains` is declared in
   `llvm_lib_translate.spl` but never implemented, so an array `.contains` has
   no correct destination today.

Regression probes for whoever fixes it: the seven rows in the symptom table
above, each with a hand-computed expectation.
