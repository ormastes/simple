# JIT Gap Reaudit — 2026-07-29 (re-measured against the current seed binary)

**ANALYSIS-ONLY.** No source was edited, nothing was built or committed. Binary
under test: `src/compiler_rust/target/release/simple`, mtime
`2026-07-29 08:46:04 UTC` (already built before this lane started — reused
as-is, not rebuilt). This binary postdates commit `d039538db7c` ("Dict.get_or
now works on both engines").

**Method:** every method still listed as a gap in
`jit_method_dispatch_audit_2026-07-29.md` (63 methods: 51 array/text/dict rows
+ dict key/value ordering + `to_float`) and
`jit_dispatch_worklist_2026-07-29.md` was re-probed with a fresh, isolated
`fn main(): ...`-wrapped `.spl` file (top-level code never JIT-compiles; a
combined probe silently demotes the whole program). Each probe was run twice:

- JIT: `SIMPLE_JIT_TRACE_ADDR=1 <seed> run probe.spl` — `[jit-addr]` in the
  output confirms the function actually compiled (vs. fell back silently).
- interp (ground truth): `SIMPLE_EXECUTION_MODE=interpreter <seed> run probe.spl`.

Two probes from the mechanical batch had bugs found and fixed during the
re-audit itself (both noted inline): `array.remove` needed `var` not `val`
(interpreter rejects a mutating call on an immutable binding — that's a
correctness signal, not a probe artifact); `text.join` must be probed as
`",".join(array)` (text is the **receiver**), not `array.join(",")` (a
different, already-fixed array method with the same name).

## Counts

| | Count |
|---|---:|
| **FIXED** (JIT == interp, `[jit-addr]` present) | **6** of 63 |
| **OPEN-NOTFOUND** (`Runtime error: Function '...' not found`, exit 0) | **43** |
| **OPEN-WRONGVALUE** (compiles, wrong/garbage/lost value) | **14** |
| **OPEN-DISPLAY** | 0 of the 63 (see bonus row below) |
| Total re-probed | 63 |

By fix-class (from the worklist's own classification):
- **CLEAN-LOWERING still open: 6** — `array.fill`, `text.substr`, `text.take`,
  `text.char_count`, `text.sorted` were **not** landed despite being
  classified "ready to implement now" in the worklist; only `sort_desc`,
  `zip`, `appended`, `prepended` from that 9-method batch actually landed.
- **NEEDS-CODEGEN still open: 14** (of 16; 2 — `array.join`, `array.enumerate`
  — are now FIXED).
- **NEEDS-F64-BOX: 0 open** — `text.to_float` (and `text.to_f64`) FIXED.
- **NEEDS-RUNTIME still open: 37/37** — none landed (expected; these need new
  Rust runtime symbols, out of scope for a lowering/codegen-only sweep).

## FIXED (6 — confirmed JIT==interp, `[jit-addr]` present)

| method | receiver | JIT | interp |
|---|---|---|---|
| `sort_desc` | array | `[5, 4, 3, 2, 1]` | `[5, 4, 3, 2, 1]` |
| `zip` | array | `[(1, 4), (2, 5), (3, 6)]` | `[(1, 4), (2, 5), (3, 6)]` |
| `join(sep)` | array | `3,1,5,2,4` | `3,1,5,2,4` |
| `enumerate` | array | `[(0, 3), (1, 1), (2, 5)]` | `[(0, 3), (1, 1), (2, 5)]` |
| `appended` | text | `abcxyz` | `abcxyz` |
| `prepended` | text | `xyzabc` | `xyzabc` |
| `to_float` (+ `to_f64` alias) | text | `3.14` | `3.14` |

Nested-tuple print and dict/array Display are both confirmed genuinely fixed
now (not just "compiles" — values match byte-for-byte), which closes the
"array.enumerate tuple print" and general float-boxing gaps the previous
audit flagged as open.

## OPEN — CLEAN-LOWERING class (6) — still just a missing dispatch arm

| method | receiver | status | JIT | interp | notes |
|---|---|---|---|---|---|
| `fill` | array | OPEN-NOTFOUND | `Function 'Array.fill' not found` | `[9, 9, 9]` | Worklist verifier flagged this may need reclass to NEEDS-RUNTIME anyway: `rt_array_fill` mutates in place but interpreter's `fill` returns a new array — a 1:1 dispatch-arm copy would be semantically wrong. |
| `substr` | text | OPEN-NOTFOUND | `Function 'str.substr' not found` | `Hello` | Alias to already-working `substring`; genuinely clean. |
| `take` | text | OPEN-NOTFOUND | `Function 'str.take' not found` | `Hello` | `take(n)` = `substring(0,n)`; genuinely clean. |
| `char_count` | text | OPEN-NOTFOUND | `Function 'str.char_count' not found` | `11` | Composed (`chars().len()`); still unlanded. |
| `sorted` | text | OPEN-NOTFOUND | `Function 'str.sorted' not found` | `abcd` | Composed (`join(sorted(chars(s)), "")`); still unlanded. |

## OPEN — NEEDS-CODEGEN class (14) — dispatch arm exists, wired wrong

| method | receiver | status | JIT | interp | notes |
|---|---|---|---|---|---|
| `remove` | array | OPEN-WRONGVALUE | returns blank, receiver unchanged `[3, 1, 5, 2, 4]` | returns `[3, 5, 2, 4]`, receiver mutated to `[3, 5, 2, 4]` | Confirmed with `var` receiver (interp rejects `val`). JIT neither mutates nor returns correctly — silent no-op. |
| `set` | dict | OPEN-WRONGVALUE | `nil` | `{a: 1, b: 2, c: 3}` | Write path compiles but the returned dict is lost. |
| `insert` | dict | OPEN-WRONGVALUE | `nil` | `{a: 1, b: 2, c: 3}` | Same lost-return-value bug as `set`. |
| `remove` | dict | OPEN-WRONGVALUE | `8` (garbage int) | `{b: 2}` | Wrong return type/ABI. |
| `clear` | dict | OPEN-WRONGVALUE | `{a: 1, b: 2}` (unchanged — no-op) | `{}` | **Reclassify vs. prior audit:** dict print is no longer a raw pointer (`<dict@0x..>` → correctly shows `{a: 1, b: 2}`), so the Display gap that the prior audit blamed is fixed, but the underlying arm is still a pure no-op — this is a real semantic bug, not just a print gap. |
| `keys` | dict | OPEN-WRONGVALUE | `[c, a, b]` (hashmap order) | `[a, b, c]` (sorted) | Values correct as a set; order violates interpreter's documented `dict_entries_sorted` contract. |
| `values` | dict | OPEN-WRONGVALUE | `[3, 1, 2]` | `[1, 2, 3]` | Same ordering-contract violation as `keys`. |
| `reverse` | text | OPEN-WRONGVALUE | `Hello World` (no-op) | `dlroW olleH` | Arm wired to nothing. |
| `clear` | text | OPEN-WRONGVALUE | `Hello World` (no-op) | `` (empty) | Same no-op wiring bug as `text.reverse`. |
| `push` | text | OPEN-WRONGVALUE | `0` | `Hello World!` | Garbage int instead of appended text. |
| `pop` | text | OPEN-WRONGVALUE | `` (blank) | `Option::Some(d)` | Value swallowed; likely shares the Option-wrap bug below. |
| `join` | text | OPEN-WRONGVALUE | `` (blank) | `a,b,c` | Must be probed as `",".join(array)` — text is the receiver. Distinct from `array.join(sep)`, which is now FIXED (see above); confirmed with a corrected probe. |
| `parse_int` | text | OPEN-WRONGVALUE | `123` (unwrapped) | `Option::Some(123)` | JIT returns the bare int instead of `Option::Some(n)` — breaks `?? default`/`.?` callers. Guide's hunch that this was closed alongside `parse_float` is **not confirmed** — still open. |
| `parse_float` | text | OPEN-WRONGVALUE | `3.14` (unwrapped) | `Option::Some(3.14)` | Same Option-unwrap bug as `parse_int`. **Correction to the reaudit-guide's assumption:** this is a distinct bug from `to_float`'s float-boxing fix — `to_float`'s boxing landed and is genuinely FIXED, but `parse_float`'s Option-wrapping did **not** land; the two are separate defects that happened to share a "float" label. |

## OPEN — NEEDS-RUNTIME class (37) — no backing `rt_*` symbol, all still not-found

All 37 confirmed unchanged from the worklist — every one still produces
`Runtime error: Function '<Recv>.<method>' not found` on JIT, `[jit-addr]`
present, exit 0, interpreter succeeds normally:

- **array (6):** `ndim`, `chunk`, `compact`, `rotate`, `fetch`, `transpose`
- **dict (6):** `merge`, `clone`, `compact`, `fetch`, `setdefault`, `dig`
- **text (25):** `capitalize`, `swapcase`, `title`, `trim_start_matches`,
  `trim_end_matches`, `removeprefix`, `removesuffix`, `chomp`, `squeeze`,
  `reversed`, `push_str`, `partition`, `rpartition`, `replace_first`,
  `repeat`, `pad_start`, `pad_end`, `center`, `zfill`, `is_numeric`,
  `is_alpha`, `is_digit`, `is_alphanumeric`, `is_whitespace`, `find_all`

Sample confirmations (representative, all follow the identical shape):
`array.ndim` → `Function 'Array.ndim' not found` (interp: `2`); `dict.merge`
→ `Function 'Dict.merge' not found` (interp: `{a: 1, b: 2}`); `text.repeat`
→ `Function 'str.repeat' not found` (interp: `ababab`); `text.reversed` →
`Function 'str.reversed' not found` (interp: `olleH`, confirming this is
still distinct from — and unfixed unlike — `text.reverse`'s no-op bug above).

## Bonus row — Object/class print (guide-flagged, outside the 63-method list)

| method | receiver | status | JIT | interp | fix-class | notes |
|---|---|---|---|---|---|---|
| `print(obj)` | class instance | OPEN-DISPLAY | `<invalid-heap:0x...>` | `Point(x: 3, y: 4)` | NEEDS-RUNTIME-METADATA | Confirms and slightly worsens the guide's expectation (`<object@ptr>`) — current output is `<invalid-heap:0x...>`, not even a valid pointer tag. Needs field-name metadata not available at JIT runtime; out of scope for a dispatch-arm or codegen fix. |

## 3 highest-value OPEN items to fix next

1. **`dict.set`/`dict.insert` returning `nil` instead of the updated dict**
   (NEEDS-CODEGEN). This silently breaks every JIT-compiled function that
   builds up a dict via chained/returned `set`/`insert` calls — the write
   itself happens (side effect lands) but the expression result is lost, so
   any code of the shape `d = d.set(k, v)` or `return d.insert(k, v)`
   silently produces `nil` with exit 0. High blast radius, and the audit
   notes the arm already compiles — this is a return-value plumbing bug, not
   new codegen.
2. **`text.parse_int`/`text.parse_float` returning the bare unwrapped value
   instead of `Option::Some(n)`** (NEEDS-CODEGEN). Any caller using the
   idiomatic `?? default` or `.?` pattern after a parse — the exact pattern
   these Option-returning APIs exist for — gets silently wrong behavior under
   JIT (a bare `3` is truthy/non-nil either way, but `?? default` on a parse
   failure won't fire the same way, and code branching on `Option::None` vs
   `Option::Some` breaks outright). This is a systemic semantic gap, not
   cosmetic, and it's isolated (both methods point at the same missing
   Option-wrap step in codegen), so one fix likely closes both.
3. **`text.reverse`/`text.clear` as silent no-ops (exit 0, unchanged value)**
   vs **`dict.clear` as the same no-op pattern**. All three currently look
   like the call succeeded (no error, `[jit-addr]`, exit 0) while doing
   nothing — the single worst failure shape in this whole sweep because
   there is no error signal at all to catch it. A shared root-cause
   investigation (why do these particular mutating-arm wirings resolve to a
   pass-through of the receiver instead of the real runtime call?) likely
   fixes 3 methods at once and is a good template for `array.remove`
   (blank-return variant of the same "arm wired wrong" family).

Runtime-symbol gaps (the 37 NEEDS-RUNTIME methods) are real but lower-urgency
per method — they fail loudly with `Function '...' not found` at exit 0
(still a silent-accept bug worth fixing, but at least diagnosable via grep for
"not found" in logs), whereas the three items above fail with a plausible-looking
value/no error at all.
