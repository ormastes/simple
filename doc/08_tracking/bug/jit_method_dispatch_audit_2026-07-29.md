# Bug: Cranelift JIT builtin-method dispatch audit — what's left after the index_of/first/last/pop/... fixes

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Date:** 2026-07-29
**Component:** `src/compiler_rust/compiler/src/codegen/instr/{calls,closures_structs,methods}.rs`,
`src/compiler_rust/compiler/src/codegen/llvm/{emitter,functions}.rs`,
vs. authoritative interpreter method sets in
`src/compiler_rust/compiler/src/interpreter_method/{collections,string}.rs`.

## Summary

This is an AUDIT only — nothing in `src/compiler_rust` was modified. A prior
session in this same day fixed several JIT dispatch gaps (`index_of`,
`first`/`last`/`pop`, `to_upper`, `strip`, `enumerate`, `lines`, `parse_int`,
dict integer keys/values, array-to-string, `Dict.insert`, `Dict.get_or`).
This audit re-probes the FULL authoritative method set (array + tuple + dict
from `interpreter_method/collections.rs`, text from
`interpreter_method/string.rs`) against a freshly built Rust-seed binary to
find what remains broken.

**Binary under test:** `src/compiler_rust/target/release/simple`, built via
`cargo build -p simple-driver --release` at this session's start.
**mtime: 2026-07-29 03:24 UTC** (fresh — confirmed by diffing content hash
against the older `bin/release/x86_64-unknown-linux-gnu/simple` from
2026-07-28 12:13, which is a different/stale binary).

**Method:** one method per probe `.spl` file (never combined — a combined
probe silently demotes the whole program and hides the JIT lane). Each probe
run twice: `SIMPLE_EXECUTION_MODE=interpret` (ground truth) and
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_TRACE_ADDR=1` (JIT under test, with
`[jit-addr]` used to distinguish "compiled but wrong" from "fell back to
interpreter"). `SIMPLE_NO_JIT` was NOT used (confirmed decoy per task brief).
15s hard timeout per run; exit code captured from the direct command, not a
pipe.

**git status of the 5 dispatch-table files + 2 interpreter files at audit
start: clean (no concurrent edits in flight from other sessions at time of
probing).**

## Totals

**142 methods probed** (51 array, 21 dict, 68 text/string, 2 special 2-D
array cases: `flatten`, `transpose`).

| Classification | Count | Meaning |
|---|---:|---|
| OK | 46 | JIT compiles (`[jit-addr]`) and result matches interpreter exactly |
| SILENT-FAIL — dispatch gap (`not found`) | 63 | `[jit-addr]` present + `Runtime error: Function '<Recv>.<method>' not found`, **process still exits 0** |
| SILENT-FAIL — wrong/garbage value | 16 | `[jit-addr]` present, no "not found", but the printed result is empty/nil, a raw pointer (`<tuple@0x..>`, `<dict@0x..>`), a raw bit-pattern (float printed as a huge integer), or a silent no-op — **exits 0** |
| ORDER-DIFF | 2 | Result set is correct but ordering violates the interpreter's documented sorted-key contract (`dict.keys()`/`dict.values()`) |
| DEMOTED (lambda-guard class) | 15 | `JIT compilation failed, falling back to interpreter:` — every method that takes a lambda argument; agrees with interpreter but never actually JIT-compiles |
| CRASH | 0 | none observed in this probe set |

All 63+16+2 = 81 "still broken but exits 0" methods are exactly the class the
task asked to find: nothing here needs a nonzero-exit convert — every one of
them is currently silently accepted as success.

## Cheap-fix candidates (missing dispatch arm, likely one-line-per-method — prioritise these first)

Ranked by rough usage-count proxy in owned code
(`rg -l '\.method(' src/lib src/compiler src/app`, counts real name collisions
with other receiver types too — treat as an upper bound, not exact):

| Method (recv) | Owned-code usage (file count, upper bound) | JIT result |
|---|---:|---|
| `insert` (array) | 69 | `Runtime error: Function 'Array.insert' not found` |
| `merge` (dict) | 53 | `Runtime error: Function 'Dict.merge' not found` |
| `clone`/`copy` (array/dict) | 52 / 23 | `Function 'Array.copy'/'Dict.clone' not found` |
| `count` (text) | 38 | `Function 'str.count' not found` |
| `repeat` (text) | 35 | `Function 'str.repeat' not found` |
| `max`/`min` (array) | 32 / 22 | `Function 'Array.max'/'Array.min' not found` |
| `entries` (dict) | 26 | `Function 'Dict.entries' not found` |
| `take`/`skip` (array) | 19 / 15 | `Function 'Array.take'/'Array.skip' not found` |
| `zip` (array) | 13 | `Function 'Array.zip' not found` |
| `sum` (array) | 12 | `Function 'Array.sum' not found` |
| `fill` (array) | 11 | `Function 'Array.fill' not found` |
| `transpose` (array) | 5 | `Function 'Array.transpose' not found` |
| `title` (text) | 4 | `Function 'str.title' not found` |
| `is_digit`/`is_alphanumeric` (text) | 4 / 4 | not found |
| `unique`/`flatten`/`find_all` (array/array/text) | 3 / 3 / 3 | not found |

Also SILENT-FAIL — dispatch gap, but 0-1 owned-code hits (still worth the
one-line fix given how cheap these are, just lower urgency): `ndim`,
`sort_desc`, `chunk`, `compact`, `rotate`, `fetch`, `sorted`, `reversed`
(array); `dig`, `setdefault`, `fetch`, `compact` (dict); `char_count`,
`capitalize`, `swapcase`, `trim_start_matches`, `trim_end_matches`,
`removeprefix`, `removesuffix`, `chomp`, `squeeze`, `reversed`, `sorted`,
`drop`, `appended`, `prepended`, `push_str`, `partition`, `rpartition`,
`replace_first`, `pad_start`, `pad_end`, `center`, `zfill`, `is_numeric`,
`is_alpha`, `is_whitespace`, `substr` (text).

**Full 63-method dispatch-gap list** (all confirmed `[jit-addr]` + `Runtime
error: Function '<Recv>.<method>' not found`, exit 0):

- **array (23):** `ndim`, `insert`, `sum`, `sort_desc`, `zip`, `take`, `skip`,
  `chunk`, `unique`, `min`, `max`, `compact`, `rotate`, `fetch`, `sorted`,
  `reversed`, `copy`, `all_truthy`, `any_truthy`, `count_of`, `fill`,
  `flatten`, `transpose`
- **dict (7):** `merge`, `clone`, `entries`, `compact`, `fetch`, `setdefault`, `dig`
- **text (33):** `char_count`, `capitalize`, `swapcase`, `title`,
  `trim_start_matches`, `trim_end_matches`, `removeprefix`, `removesuffix`,
  `chomp`, `squeeze`, `reversed`, `sorted`, `take`, `drop`, `appended`,
  `prepended`, `push_str`, `partition`, `rpartition`, `replace_first`,
  `repeat`, `pad_start`, `pad_end`, `center`, `zfill`, `is_numeric`,
  `is_alpha`, `is_digit`, `is_alphanumeric`, `is_whitespace`, `count`,
  `substr`, `find_all`

## Runtime-function-needed candidates (wrong/garbage value class — likely needs more than a dispatch arm)

These already have SOME dispatch arm (no "not found", `[jit-addr]` present)
but return the wrong thing — the arm exists and is wired to a codegen path,
but the codegen path itself is broken (missing runtime call, wrong ABI, or a
`print`/Display gap for the returned type under JIT). Each needs its own
root-cause, not a one-line copy of the interpreter's dispatch entry:

| Method | Interp result | JIT result | Likely defect class |
|---|---|---|---|
| `text.to_float` | `3.14` | `599605265959989376` | raw tag-boxed float bit pattern printed as int — same family as the known `list.get(i)<<3` bug |
| `text.reverse` | `dlroW olleH` | `Hello World` (unchanged) | dispatch arm is a no-op / wrong alias wiring (note: `array.reverse` is OK, `text.reversed` is a separate not-found gap — `text.reverse` alone is silently wrong) |
| `text.clear` | `` (empty) | `Hello World` (unchanged) | no-op, same shape as `text.reverse` |
| `text.push`/`text.pop`/`text.join` | `Hello World!` / `Option::Some(d)` / `a,b,c` | `0` / *(blank)* / *(blank)* | garbage int or swallowed value |
| `text.is_empty` | `false` | `0` | Bool printed as raw int under JIT (Display/print gap, not just this method) |
| `text.parse_int`/`text.parse_float` | `Option::Some(123)` / `Option::Some(3.14)` | `123` / `3.14` | JIT returns the unwrapped value instead of `Option::Some(..)` — semantic, not just cosmetic (breaks `?? default` and `.?` callers) |
| `array.remove` | `[3, 5, 2, 4]` | *(blank)* | nil/garbage on a non-place receiver |
| `array.join` | `3,1,5,2,4` | `,,,,` | elements read as empty strings — matches the prior session's "array-to-string" bug family; may be only partially fixed |
| `array.enumerate` | `[(0, 3), (1, 1), ...]` | `[<tuple@0x..>, ...]` | tuple-in-array Display/print gap under JIT (enumerate itself already listed as fixed this session — the fix made it COMPILE, but nested-tuple printing is a separate, still-open gap) |
| `dict.set`/`dict.insert` | full updated dict | `nil` | write path exists (compiles) but the returned dict value is lost |
| `dict.remove` | reduced dict | `8` (garbage) | wrong return type/ABI |
| `dict.clear` | `{}` | `<dict@0x..>` (raw pointer) | empty-dict Display/print gap under JIT |

## Ordering-contract violation (low severity, but real)

`dict.keys()` / `dict.values()`: interpreter explicitly guarantees
sorted-by-key order (`dict_entries_sorted`, documented in
`interpreter_method/collections.rs:912-916`); JIT returns raw hashmap order
(`[c, a, b]` vs `[a, b, c]` for keys). Values match as a *set*, not as a
*sequence* — any code depending on `keys()[i]`/`values()[i]` describing the
same entry (the exact case the interpreter comment calls out) is silently
wrong under JIT.

## Lambda-demotion class (DEMOTED, not itself a bug — noted for completeness)

Every method taking a lambda argument currently reports
`JIT compilation failed, falling back to interpreter:` and never compiles:
array `map`, `filter`, `reduce`, `find`, `any`, `all`, `flat_map`,
`take_while`, `skip_while`, `count`, `partition`, `group_by`; dict
`map_values`, `filter`; text `with`. Values agree with the interpreter (not a
correctness bug), but none of these get real JIT speed — this is the known
"lambda-guard" gap, distinct from the dispatch-table gaps above and out of
scope for a one-line fix (needs closure/lambda codegen support).

## What's confirmed OK (46/142 — no action needed)

array: `len`, `length`, `is_empty`, `first`, `last`, `get`, `contains`,
`push`, `pop`, `concat`, `reverse`, `slice`, `index_of`, `sort`, `clear`.
dict: `len`, `is_empty`, `contains_key`, `has`, `get`, `get_or`. text: `len`,
`chars`, `bytes`, `contains`, `starts_with`, `ends_with`, `find`,
`index_of`, `to_upper`, `to_lower`, `trim`, `strip`, `trim_start`,
`trim_end`, `split`, `lines`, `replace`, `slice`, `substring`,
`last_index_of`, `rfind`, `to_int`, `char_at`, `ord`, `char_code_at`.

## Recommended fix order

1. **Cheap dispatch-arm gaps, high usage** — `Array.insert`, `Dict.merge`,
   `Array.copy`/`Dict.clone`, `str.count`, `str.repeat`, `Array.max`/`min`,
   `Dict.entries`, `Array.take`/`skip`, `Array.zip`, `Array.sum`,
   `Array.fill`. Each is a pure value-in/value-out method already fully
   implemented in the interpreter (see line refs in
   `interpreter_method/collections.rs`/`string.rs` above) — same shape as the
   already-fixed `index_of`/`first`/`last` batch.
2. **Cheap dispatch-arm gaps, low usage** — remaining 47 methods in the full
   list above; still one-line-class fixes, just less urgent.
3. **Wrong-value class** — `text.to_float` (tag-boxed float bug, same family
   as a known reference bug), `text.parse_int`/`parse_float` (Option-wrapping
   dropped), `dict.set`/`insert`/`remove`/`clear`, `array.join`/`remove`,
   `array.enumerate` nested-tuple print. These need actual root-cause per
   method, not a copy-paste dispatch arm — recommend a dedicated follow-up
   session per method or a shared root cause if `print`/Display formatting
   under JIT turns out to be one gap touching several of these.
4. **Ordering contract** — `dict.keys()`/`values()` need JIT to route through
   the same `dict_entries_sorted` order the interpreter uses.
5. **Lambda-demotion class** — separate, larger effort (closure/lambda JIT
   codegen); track separately from the dispatch-table gaps.

## Raw evidence

Probe generator, probe `.spl` files, per-method interpreter/JIT output pairs,
and the full classified CSV are preserved at `/tmp/jitaudit/` on the host
that ran this audit (`results.csv`, `out/*.interp.out`, `out/*.jit.out`,
`array_probes.txt`, `dict_probes.txt`, `text_probes.txt`, `run_audit.sh`) —
not committed to the repo (scratch, not requested for git).

## 2026-07-29 — root causes established for 3 text value gaps + dispatch batch progress

**Landed this session (JIT dispatch-boxing, verified JIT==interp, [jit-addr]):**
- 3fbf9c1 — count/drop/entries/insert/max/min/skip/sum/take (9)
- 7c5792c — array copy/unique/sorted/reversed/flatten/all_truthy/any_truthy/count_of (8)
- 725337d — text.is_empty typed BOOL (was raw int)
- ee4800f — Option/Result is_some/is_none/is_ok/is_err for ANY/NIL receivers
  (guards only fired for statically-resolved enum types; Some(x)/Ok(x) are ANY,
  None is NIL → fell through to not-found. Backed by existing
  rt_is_some/rt_is_none/rt_enum_check_discriminant.)

**Text value gaps — precise root causes (NOT quick lowering fixes):**
- `text.to_float()` → JIT prints the raw f64 **bit pattern** as an int
  (`"3.14"` → `599357747061063936`). The HIR result-type entry IS already F64
  (`hir/lower/expr/mod.rs:52,1214`), so unlike the int/bool gaps a result-type
  entry is NOT sufficient. The F64 result is not heap-boxed (`rt_value_float`)
  before flowing into `.to_string()`/print — that boxing lives in **codegen**
  (Cranelift instr emitters), not lowering. Likely SYSTEMIC to every
  float-returning method. Needs a codegen lane, not a lowering arm.
  (`rt_string_to_float` runtime symbol exists at collections.rs:2689.)
- `text.reverse()` → JIT **no-op** (`"Hello"` → `Hello`); `text.reversed()` →
  **not found**. There is NO `rt_string_reverse`/`rt_string_reversed` runtime
  symbol (only `rt_array_reversed` at collections.rs:3114). Fixing these needs a
  NEW runtime Rust function + bootstrap — out of lowering scope.

**Lambda ABI** still blocked — see jit_lambda_abi_scoping_2026-07-29.md
(rt_closure_new never declared in the runtime-import table).

## 2026-08-17 note (lane s2_rust_codegen) — LIVE, but one supporting evidence line is unsound

This audit stays OPEN. No claim here is being closed.

One correction to the triage evidence attached to this row, which read: *"grep
`rt_string_reverse` returns ZERO hits, so at least one listed gap is still real."*
That inference does not hold. The implemented design deliberately never
introduces a symbol named `rt_string_reverse`; `reverse` is wired to the
**receiver-polymorphic** `rt_reverse_mut`, which handles a text receiver directly
(`src/compiler_rust/runtime/src/value/collections.rs:3071`,
`s.chars().rev().collect()`), with the codegen arms at
`codegen/instr/calls.rs:3656`, `codegen/instr/closures_structs.rs:2028` and
`codegen/llvm/emitter.rs:292`. See the companion note added the same day to
`jit_dispatch_worklist_2026-07-29.md`.

So the `reverse` cell is stale. The audit's substantive finding — that enum
guards fire only for statically-resolved types, leaving `Some(x)`/`Ok(x)` as
`ANY` — was **not** re-checked here and is untouched by the above. Keep this row
open on that finding, not on the `reverse` cell.

### Could NOT prove
The enum-guard / `ANY` finding in the title was not re-verified, and none of the
audit's 63 enumerated methods were executed. Source inspection of the `reverse`
cell only.
