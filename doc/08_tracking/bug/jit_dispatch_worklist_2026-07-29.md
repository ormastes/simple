# JIT Method-Dispatch Worklist — remaining gaps after 2026-07-29 sweeps

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Derived from `doc/08_tracking/bug/jit_method_dispatch_audit_2026-07-29.md`.
Already-landed methods are NOT relisted: `count`/`drop`/`entries`/`insert`/
`max`/`min`/`skip`/`sum`/`take` (array insert/max/min/skip/sum/take, dict
entries, text count/drop); array `copy`/`unique`/`sorted`/`reversed`/
`flatten`/`all_truthy`/`any_truthy`/`count_of`; `text.is_empty`; Option/Result
`is_some`/`is_none`/`is_ok`/`is_err`.

Runtime symbol inventory used below: full `rt_array_*`/`rt_dict_*`/
`rt_string_*` export list grepped from
`src/compiler_rust/runtime/src/value/` at analysis time (142 total; no build
run, no probes executed — this is a static read of the audit doc + a symbol
grep + existing dispatch-arm shapes in
`src/compiler_rust/compiler/src/codegen` / `mir/lower/lowering_expr_method.rs`).

## CLEAN-LOWERING — priority backlog (9 methods, 2 batches)

### Batch 1 — array (3 methods)

| method | receiver | runtime symbol | result type | fix class | notes |
|---|---|---|---|---|---|
| `sort_desc` | array | `rt_array_sort_desc` (exists) | array (in-place, mirrors `sort`) | CLEAN-LOWERING | Same shape as already-fixed `array.sort`/`array.sorted`; just needs the dispatch arm + result-type entry. |
| `fill` | array | `rt_array_fill` (exists) | array (in-place) | CLEAN-LOWERING | Direct 1:1 symbol match, same pattern as the landed batch. |
| `zip` | array | `rt_array_zip` (exists) | array<tuple> | CLEAN-LOWERING | Dispatch arm is clean, but result is an array of tuples — verify against the still-open `array.enumerate` nested-tuple print gap (NEEDS-CODEGEN below) before declaring this one fully done; the dispatch fix itself is still one-line. |

### Batch 2 — text (6 methods)

| method | receiver | runtime symbol | result type | fix class | notes |
|---|---|---|---|---|---|
| `appended` | text | `rt_string_concat` (exists) | text | CLEAN-LOWERING | `appended(x)` = `concat(self, x)`; no new symbol, reuse existing concat call. |
| `prepended` | text | `rt_string_concat` (exists) | text | CLEAN-LOWERING | `prepended(x)` = `concat(x, self)`; reversed operand order on the same existing call. |
| `substr` | text | `rt_string_*` used by `substring` (exists, already OK) | text | CLEAN-LOWERING | Alias to the already-working `substring`/`slice` codegen path — same runtime call, just a second dispatch-table entry name. |
| `take` | text | same as `substring` (exists) | text | CLEAN-LOWERING | `take(n)` = `substring(0, n)`; reuse existing substring codegen, no new symbol. |
| `char_count` | text | `rt_string_chars` + `rt_array_len` (both exist) | int | CLEAN-LOWERING | Compose two existing calls (`chars().len()`); more than one runtime call but zero new Rust. Note: don't use for hot loops — see `char_code_at` O(n) pitfall in memory notes. |
| `sorted` | text | `rt_string_chars` + `rt_array_sorted` + `rt_string_join` (all exist) | text | CLEAN-LOWERING | Compose: `join(sorted(chars(s)), "")`. All three symbols already exist and are already used by other landed fixes (`chars`, `array.sorted`, `join`) — no new runtime needed, just glue in lowering. |

## NEEDS-CODEGEN (16 methods) — dispatch arm exists, output is wrong; root-cause each, no copy-paste fix

| method | receiver | runtime symbol | result type | fix class | notes |
|---|---|---|---|---|---|
| `remove` | array | none named `rt_array_remove` found — likely built from existing get/set/shift primitives already wired in an arm | array | NEEDS-CODEGEN | Compiles (`[jit-addr]`), returns blank — "nil/garbage on a non-place receiver" per audit; needs a receiver-mutation root cause, not a new dispatch arm. |
| `join` | array | `rt_array_join` (exists) | text | NEEDS-CODEGEN | Elements read as empty strings (`,,,,`) — same family as the prior "array-to-string" bug, may be only partially fixed. |
| `enumerate` | array | `rt_array_enumerate` (exists) | array<tuple> | NEEDS-CODEGEN | Already compiles; nested-tuple Display/print gap under JIT (`<tuple@0x..>`) — blocks `zip` above too. |
| `reverse` | text | none (`rt_string_reverse` does not exist) but arm already present as a no-op | text | NEEDS-CODEGEN / NEEDS-RUNTIME (blended) | Existing arm is wired to nothing (silent no-op), so it's a wrong-wiring bug on top of a missing symbol. See `reversed` below for the real runtime gap. |
| `clear` | text | none dedicated; arm already present as a no-op | text | NEEDS-CODEGEN | Same shape as `text.reverse` — arm exists, wired wrong (no-op instead of returning empty text). Could resolve cheaply via `rt_string_new_literal("")` once the wiring bug is found. |
| `push` | text | unclear — arm present, returns garbage int `0` | text/unit | NEEDS-CODEGEN | Needs its own root-cause per audit; receiver semantics (mutable buffer vs immutable Text) unclear from static read. |
| `pop` | text | unclear — arm present, returns blank instead of `Option::Some(d)` | Option<char> | NEEDS-CODEGEN | Likely shares the Option-wrapping bug seen in `parse_int`/`parse_float` below. |
| `join` | text | unclear semantics (Text.join?) — arm present, returns blank | text | NEEDS-CODEGEN | Audit groups this with `push`/`pop`; needs its own probe to even confirm the intended receiver/signature. |
| `parse_int` | text | `rt_string_to_int` / `rt_string_to_int_lenient` (exist) | Option<int> | NEEDS-CODEGEN | Arm exists and calls the right runtime function, but JIT returns the unwrapped int instead of `Option::Some(n)` — semantic Option-wrapping bug, breaks `?? default`/`.?` callers. |
| `parse_float` | text | `rt_string_to_float` (exists) | Option<float> | NEEDS-CODEGEN | Same Option-unwrap bug as `parse_int`; also intersects the F64-boxing gap below once Option wrapping is fixed. |
| `set` | dict | `rt_dict_set` (exists) | dict | NEEDS-CODEGEN | Write path compiles but the returned dict value is lost (`nil`) — return-value plumbing bug, not a missing arm. |
| `insert` | dict | `rt_dict_set` (exists, likely same arm as `set`) | dict | NEEDS-CODEGEN | Grouped with `dict.set` in the audit — same lost-return-value bug. |
| `remove` | dict | `rt_dict_remove` (exists) | dict | NEEDS-CODEGEN | Returns garbage int (`8`) instead of the reduced dict — wrong return type/ABI on an existing call. |
| `clear` | dict | `rt_dict_clear` (exists) | dict | NEEDS-CODEGEN | Returns raw pointer (`<dict@0x..>`) — empty-dict Display/print gap under JIT, same family as `array.enumerate`'s tuple-print gap. |
| `keys` (ordering) | dict | `rt_dict_keys` (exists, unsorted) | array<text/any> | NEEDS-CODEGEN | Values correct as a set, order violates interpreter's documented `dict_entries_sorted` contract. May need a new `rt_dict_keys_sorted` export if sorting can't be done cheaply in lowering — flag for a build-time check before assuming pure codegen fix. |
| `values` (ordering) | dict | `rt_dict_values` (exists, unsorted) | array<any> | NEEDS-CODEGEN | Same ordering-contract gap as `keys`, same caveat about a possible new sorted-export need. |

## NEEDS-F64-BOX (1 method) — blocked on in-flight float-boxing codegen fix

| method | receiver | runtime symbol | result type | fix class | notes |
|---|---|---|---|---|---|
| `to_float` | text | `rt_string_to_float` (exists) | float | NEEDS-F64-BOX | HIR result-type entry is already F64; the raw f64 bit pattern isn't heap-boxed (`rt_value_float`) before flowing into `.to_string()`/print. In flight per audit's 2026-07-29 root-cause note — likely systemic to every float-returning method, needs a Cranelift codegen lane not a lowering arm. |

## NEEDS-RUNTIME (37 methods) — no backing rt_* symbol, needs new Rust + bootstrap

| method | receiver | runtime symbol | result type | fix class | notes |
|---|---|---|---|---|---|
| `ndim` | array | NONE | int | NEEDS-RUNTIME | No 2-D shape introspection symbol exists. |
| `chunk` | array | NONE | array<array> | NEEDS-RUNTIME | Needs a new grouping runtime fn. |
| `compact` | array | NONE | array | NEEDS-RUNTIME | Filter-nil-out semantics; no existing symbol. |
| `rotate` | array | NONE | array | NEEDS-RUNTIME | No rotate-by-n symbol. |
| `fetch` | array | NONE | any (with default) | NEEDS-RUNTIME | Ruby-`Hash#fetch`-style default/raise semantics; distinct from plain `get`. |
| `transpose` | array | NONE | array<array> | NEEDS-RUNTIME | 2-D case, audit's other special case besides `flatten` (which is already fixed). |
| `merge` | dict | NONE | dict | NEEDS-RUNTIME | High owned-code usage (53) — prioritize within this class. |
| `clone` | dict | NONE | dict | NEEDS-RUNTIME | No `rt_dict_copy`/`rt_dict_clone` equivalent to `rt_array_copy`. |
| `compact` | dict | NONE | dict | NEEDS-RUNTIME | Filter-nil-values semantics. |
| `fetch` | dict | NONE | any (with default) | NEEDS-RUNTIME | Same default/raise semantics as array's `fetch`. |
| `setdefault` | dict | NONE | dict/any | NEEDS-RUNTIME | Needs insert-if-absent runtime fn. |
| `dig` | dict | NONE | any | NEEDS-RUNTIME | Nested-path lookup, no existing symbol. |
| `capitalize` | text | NONE | text | NEEDS-RUNTIME | |
| `swapcase` | text | NONE | text | NEEDS-RUNTIME | |
| `title` | text | NONE | text | NEEDS-RUNTIME | Owned-code usage 4. |
| `trim_start_matches` | text | NONE | text | NEEDS-RUNTIME | Pattern-arg variant of existing `trim_start`. |
| `trim_end_matches` | text | NONE | text | NEEDS-RUNTIME | Pattern-arg variant of existing `trim_end`. |
| `removeprefix` | text | NONE | text | NEEDS-RUNTIME | |
| `removesuffix` | text | NONE | text | NEEDS-RUNTIME | |
| `chomp` | text | NONE | text | NEEDS-RUNTIME | |
| `squeeze` | text | NONE | text | NEEDS-RUNTIME | |
| `reversed` | text | NONE (`rt_string_reverse`/`rt_string_reversed` do not exist; only `rt_array_reversed`) | text | NEEDS-RUNTIME | Guide-flagged known-hard. A compose-from-existing-symbols path (`join(reversed(chars(s)), "")` using `rt_string_chars`+`rt_array_reversed`+`rt_string_join`, mirroring the `sorted` CLEAN-LOWERING entry above) may make this cheaper than a brand-new Rust symbol — worth a build-time spot-check before committing to the NEEDS-RUNTIME path, but keeping the guide's classification here since it was explicitly called out as needing a new symbol. |
| `push_str` | text | NONE | text/unit | NEEDS-RUNTIME | In-place mutation on a value the rest of the audit shows is otherwise immutable under JIT (`clear`/`push`/`pop` also broken) — likely needs a mutable-text/StringBuilder-backed runtime path, not just a new pure fn. |
| `partition` | text | NONE | tuple<text,text,text> | NEEDS-RUNTIME | Also inherits the tuple-print gap once a symbol exists. |
| `rpartition` | text | NONE | tuple<text,text,text> | NEEDS-RUNTIME | Same as `partition`. |
| `replace_first` | text | NONE | text | NEEDS-RUNTIME | Single-occurrence variant of existing `replace`. |
| `repeat` | text | NONE | text | NEEDS-RUNTIME | Owned-code usage 35 — high priority within this class. |
| `pad_start` | text | NONE | text | NEEDS-RUNTIME | |
| `pad_end` | text | NONE | text | NEEDS-RUNTIME | |
| `center` | text | NONE | text | NEEDS-RUNTIME | |
| `zfill` | text | NONE | text | NEEDS-RUNTIME | |
| `is_numeric` | text | NONE | bool | NEEDS-RUNTIME | Per-char predicate scan; needs a Rust loop fn, not just a dispatch arm (no cheap single-call composition available). |
| `is_alpha` | text | NONE | bool | NEEDS-RUNTIME | Same as `is_numeric`. |
| `is_digit` | text | NONE | bool | NEEDS-RUNTIME | Same as `is_numeric`; owned-code usage 4. |
| `is_alphanumeric` | text | NONE | bool | NEEDS-RUNTIME | Same as `is_numeric`; owned-code usage 4. |
| `is_whitespace` | text | NONE | bool | NEEDS-RUNTIME | Same as `is_numeric`. |
| `find_all` | text | NONE | array<int> | NEEDS-RUNTIME | Only single-match `find`/`index_of` exist; multi-occurrence scan needs new Rust. Owned-code usage 3. |

## Summary

- **CLEAN-LOWERING: 9** (array: `sort_desc`, `fill`, `zip`; text: `appended`, `prepended`, `substr`, `take`, `char_count`, `sorted`) — 2 batches, ready to implement now.
- **NEEDS-CODEGEN: 16**, **NEEDS-F64-BOX: 1** (`text.to_float`, in flight), **NEEDS-RUNTIME: 37** (6 array + 6 dict + 25 text).
- Total distinct still-open methods covered: 63 (matches the audit's 63 not-found + 16 wrong-value + 2 ordering-contract minus the already-swept overlaps).

## Verifier notes (parent lane, 2026-07-29)
- `array.fill` is NOT clean 1:1: `rt_array_fill` mutates in place but the
  interpreter's `fill` returns a NEW array. DISPATCH2 already skipped it for this
  reason. Reclassify as NEEDS-RUNTIME (a non-mutating `rt_array_filled`) or drop.
- Batch-2 `char_count`/`sorted` are COMPOSED (multiple runtime calls), not a
  single dispatch arm — more than the landed pattern; verify the composition
  boxes correctly and JIT-compiles before trusting them. `appended`/`prepended`
  (→rt_string_concat) and `substr`/`take` (→substring path) are the clean ones.
- Every candidate MUST be re-confirmed on a `fn main()`-wrapped probe on the
  freshly-built seed (JIT==interp, [jit-addr]) before landing — the worklist was
  inferred from grep, not run.

## 2026-08-17 partial re-verification (lane s2_rust_codegen) — the `text.reverse` row is STALE

Classified by CONTENT of current source, not by commit ancestry.

The worklist row for `reverse` (table line 48) states: *"none (`rt_string_reverse`
does not exist) but arm already present as a no-op … wired to nothing (silent
no-op)"*. That is no longer true, and the triage evidence line
"`grep -rl rt_string_reverse` returns ZERO hits: runtime fn still absent" is a
mis-specified test — the implemented design deliberately never introduces a
symbol by that name.

Current source wires `reverse` to the **receiver-polymorphic** `rt_reverse_mut`:
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:3656` — `"reverse" => Some("rt_reverse_mut")`
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2028` — `"reverse" => "rt_reverse_mut"`
- `src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:292` — same mapping, with
  the assertion at `emitter.rs:2350` pinning it.

And that callee genuinely handles a **text** receiver, not just arrays —
`src/compiler_rust/runtime/src/value/collections.rs` `rt_reverse_mut`: the array
branch is tried first (`:3066`), and the text branch at `:3071` returns
`new_string(&s.chars().rev().collect::<String>())`, falling through to
`refuse_non_text_receiver("reverse")` (`:3072`) only for a receiver that is
neither. So there is no silent no-op on this arm.

**Do not close the whole worklist on this.** Only the `reverse` cell is settled.
The rest of the 63-method worklist was not re-verified here and should be assumed
live — including the rows this lane spot-checked nothing for (`sort_desc`, `zip`,
`join`, `parse_float`, `transpose`) and the sibling `reversed` row at line 93,
which is a genuinely different method and was NOT checked.

### Could NOT prove
No execution was run for this row; the evidence is source-level only. The
neighbouring `text.clear` row (line 49), described as the same "arm exists, wired
wrong" shape, was NOT checked and may still be a live silent no-op.

## Content re-verification 2026-08-17 (m2_rust_compiler lane) — CONFIRMED STILL OPEN

`rt_string_reverse` is absent from every runtime in the tree. Scoped grep over
`src/compiler_rust/compiler/src`, `src/compiler_rust/runtime/src` and `src/runtime`
returns only `src/runtime/runtime_native.c:4644 static int64_t rt_string_reverse_chars(RtCoreString*)`
(file-local, used at :4684 and :4722, never exported). `grep -n reverse` over
`src/compiler_rust/compiler/src/codegen/instr/methods.rs` returns zero hits — the
`reverse` arm does not exist there at all any more, so the "no-op arm" description is
stale in form but the gap is real in substance.

Fixing this needs a new exported `rt_string_reverse` in `src/compiler_rust/runtime/src`
plus a `RuntimeFuncSpec` and a dispatch arm; the runtime crate is outside the
`src/compiler_rust/compiler/**` scope of this lane, so it was not attempted.
Wiring the arm alone would emit a call to a nonexistent symbol.
