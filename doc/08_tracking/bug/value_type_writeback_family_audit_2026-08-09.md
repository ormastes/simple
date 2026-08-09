# Value-type write-back family audit (2026-08-09)

Follow-up sweep to `e5bc26ced33`, which fixed two defects in
`src/compiler/70.backend/backend/env.spl` (doubly-indexed assignment target;
descending inclusive range). This doc enumerates the two bug FAMILIES across
owned code so siblings are not left behind.

## Measured container semantics (interpreter/seed lane)

Probed directly with `bin/simple run` on the Rust bootstrap seed (the lane
compiler `.spl` edits are live on). Results are **not** uniform, which is why
the family cannot be swept by spelling alone:

| shape | result |
|---|---|
| `arr.push(x)` bare statement (local **or** `self.field`) | mutates IN PLACE — correct |
| `arr.pop()` bare statement (local **or** `self.field`) | mutates IN PLACE, returns the REMOVED ELEMENT |
| `x = x.pop()` | **BUG** — assigns the removed element over the array |
| `dict.set(k,v)` bare statement | mutates IN PLACE — correct |
| `var row = arr2d[i]; row[j] = v` with no `arr2d[i] = row` | **mutation LOST** |
| `val inner = dictOfDict[k]; inner[k2] = v` with no write-back | mutation PROPAGATES |

The array-of-array row copy loses the write; the dict-of-dict inner copy does
not. Both are lane-observed on the seed interpreter only — **native/JIT lanes
were not probed** and may differ (see `dict_native_pitfalls.md`).

## Family A — descending inclusive ranges: CLEAN

`/usr/bin/grep -rn '\.\.=' src/ --include=*.spl` → 50 hits (exit 0; control
search `me pop_scope` → 7 hits, proving the scan was live and not a timed-out
empty). All 50 reviewed:

- 46 are ascending literal bounds (`0..=n`, `1..=m`) — correct.
- 2 are prose comments inside `env.spl` describing the already-fixed bug.
- 3 are the interpreter *implementing* user-level ranges with runtime bounds
  (`start..=end` at `src/app/interpreter/control/control/loops.spl:281`,
  `src/app/interpreter/expr/advanced.spl:67`,
  `src/app/interpreter/utils/slicing.spl:88`). Empty-on-`start > end` is the
  intended language semantic here, not a defect.
- 1 (`src/compiler_rust/lib/std/src/tooling/format_utils.spl:239`) is out of
  owned scope (Rust seed tree) and uses stepped-range syntax.

**No remaining defects in this family.**

## Family B — value-type write-back

### FIXED — `levenshtein_distance` returned 0 for every input

`src/lib/common/text_advanced.spl:518`. The DP matrix rows were copied out of
`dp` (`var row_i = dp[i]`, `var cur_row = dp[i]`), mutated, and never written
back, so the matrix stayed zero-filled at all three sites. Measured before the
fix:

```
lev(kitten,sitting)=0   expect 3
lev(abc,xyz)=0          expect 3
```

Fixed by adding `dp[i] = row_i` / `dp[0] = row_0` / `dp[i] = cur_row`.
Regression guard: `test/01_unit/lib/common/text_advanced_levenshtein_spec.spl`
(7 examples, every oracle asserts a NON-ZERO distance — an equal-string case
cannot detect this defect because 0 is also its correct answer). Sabotage-proved:
removing the inner write-back takes the spec from 7/7 to 2/7.

### NOT A DEFECT on this lane — `register_trait`

`src/compiler/30.types/associated_types_defs.spl:221` copies an inner dict out
of `self.traits["traits"]` and mutates it without a write-back. This *looks*
like the `define`/`assign` bug but dict-of-dict copy-out propagates on the
measured lane, so registration is not lost. Left unchanged. **Caveat:** this
relies on an unspecified aliasing behaviour that differs from the array case;
if the native lane is ever probed and diverges, this becomes a live defect.
Adding an explicit write-back would be harmless and more honest, but is a
behaviour-neutral change on the only lane we can currently measure, so it is
recorded here rather than made blind.

### OPEN / needs a reference-vs-value ruling — pure_database

`src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:2839`:

```
var tbl = self._tbl_data[ti]
tbl.delete_matching(tid, old_data)
tbl.insert(tid, _serialize_row(new_vals))
var typed2 = self._tbl_typed[ti]; typed2.push(new_vals); self._tbl_typed[ti] = typed2
```

The sibling `typed2` gets an explicit `self._tbl_typed[ti] = typed2` write-back
but `tbl` does not. Whether that asymmetry is a defect depends on whether
`_tbl_data` elements are value structs (defect — the UPDATE is silently
dropped) or classes (benign — reference semantics). Not resolved here: the
surrounding UPDATE path has no spec coverage to discriminate against, and
guessing risks either a silent no-op fix or a double-apply.

**Unblock condition:** a spec that performs a SQL `UPDATE` through
`pure_database` and then reads the row back, asserting the new value. If that
spec is red, add `self._tbl_data[ti] = tbl`.

## Not-a-bug: `pop_scope`

`Environment.pop_scope` was suspected of being a no-op because it discards
`self.scopes.pop()`'s result. It is **correct as written** — `.pop()` mutates
in place. The proposed "fix" (`self.scopes = self.scopes.pop()`) would have
been a regression, assigning the removed scope dict over the scope array.
Both the no-op and the write-back variants were sabotage-tested and both take
the new behavioural spec red. Guard added at
`test/01_unit/compiler/backend/interpreter_backend_spec.spl` ("tears down a
popped scope so its names stop resolving") replacing reliance on the
pre-existing source-grep-only check.
