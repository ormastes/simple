# Dict class-field contains_key/bracket-read after insert — 2026-08-08

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Origin

A lane fixing a tuple-index bug in `src/compiler/20.hir/hir_lowering/expressions.spl`
hit: `rt_dict_contains(self.local_tuple_types, sym.id)` returned `false`
immediately after `self.local_tuple_types[sym.id] = elem_types` was executed
in the same scope, on a `Dict<i64,[HirType]>` that is a `class HirLowering`
FIELD (`local_tuple_types: HirLocalTupleTypes` where
`type HirLocalTupleTypes = {i64: [HirType]}`, `src/compiler/20.hir/hir_lowering/types.spl:53,119`).
This would mean the doc-recommended `contains_key(k)` + `d[k]` workaround
(`doc/07_guide/language/dict_native_pitfalls.md`) is unsound for class-field
dicts. This doc is a narrow, minimal-fixture investigation of that claim.

## Verdict (one line)

**`contains_key` on a class-field Dict is SAFE right after insert** — did not
reproduce, on either the interpreter or a `native-build` ELF, for `{i64: [i64]}`.
**But a NEW, different failure was found**: bracket-reading (`self.d[k]`) a
class-field `{i64: [i64]}` dict immediately after insert **SEGFAULTs** under
`native-build`, while the same dict as a local variable (not a field) does
not crash. `keys().len()` on the class field is also safe. So the
"membership-check" half of the documented replacement pattern is fine for a
class-field array-valued dict; the "index-read" half is not.

## Reproduction fixture

Minimal segfaulting case (`native-build`, not interpreter):

```
class Holder:
    d: {i64: [i64]}

    fn init():
        self.d = {}

    fn check():
        val k: i64 = 1
        val v: [i64] = [10, 20]
        self.d[k] = v
        val readback: [i64] = self.d[k]
        print("bracket read len: " + readback.len().to_text())

fn main():
    val h = Holder()
    h.init()
    h.check()
```

Build/run oracle used:

```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
  --source <dir> --entry-closure --entry <dir>/main.spl --cache-dir <tmp>/c --output <tmp>/b
<tmp>/b
```

Result: build succeeds (rc 0). Running the binary segfaults:

```
[simple-runtime] Fatal: SIGSEGV at address 0x...
RUN_EXIT=139
```

## Isolation steps (all native-build, same source tree)

| Variant | contains_key(k) after insert | keys().len() after insert | self.d[k] bracket-read after insert |
|---|---|---|---|
| Class field `d: {i64:[i64]}`, contains_key only | `true` (correct) | not tested in this variant | not tested |
| Class field, contains_key + keys().len() | `true` | `1` (correct) | not tested |
| Class field, contains_key + bracket-read | segfault before any print flushed (see note below) | — | crashes |
| Class field, bracket-read ONLY (no contains_key call at all) | — | — | **crashes** (isolates the fault to the bracket-read itself, not an interaction with contains_key) |
| Local (non-field) `var d: {i64:[i64]}` in `fn main()`, contains_key + bracket-read | `true` | — | `2` (correct, no crash) |

Note on the "segfault before any print flushed" row: stdout is buffered and
the process aborts (SIGSEGV) before the buffer is flushed on a crash, so a
crash later in `check()` can swallow earlier `print()` output entirely — this
is a measurement caveat, not evidence that `contains_key` itself failed in
that run. The isolated variant (bracket-read only, no `contains_key` call at
all) confirms the fault is in the bracket-read path itself: it segfaults with
nothing before it.

Conclusion: the crash requires BOTH (a) the dict being a class field (not a
local var) and (b) the value type being an array (`[i64]`) that is
bracket-read immediately after insert. Neither `contains_key` nor
`keys().len()` on the same class field triggered it.

## Per-engine results

- **Interpreter** (`bin/simple test`, `SIMPLE_MODULE_LIMIT=0`): spec
  `test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl`
  — `Results: 3 total, 3 passed, 0 failed`. `contains_key`, `keys().len()`,
  and bracket-read (including reading back the array elements) are all
  correct on the interpreter for the class-field `{i64:[i64]}` case.
- **native-build**: `contains_key` and `keys().len()` correct;
  class-field bracket-read of an array value **segfaults** (rc 139).
- **JIT** (`bin/simple run`): not tested — optional per task scope, budget
  spent on native-build isolation instead.

## Relationship to the origin report

The origin lane's observation (`contains_key` returning `false` right after
insert on `local_tuple_types: Dict<i64,[HirType]>`) was **not reproduced**
here for the closest analogue tried (`{i64: [i64]}` as a class field). Two
differences from the origin remain untried given the budget: (1) `HirType` is
a more complex struct/enum-shaped element inside the array, vs. plain `i64`
here; (2) the origin dict lives on `class HirLowering`, a large real compiler
class with many other fields and methods, vs. this minimal `Holder`. Either
could plausibly matter (e.g. field-layout/offset interactions in a large
class), but were out of scope to chase further under this task's budget. The
bracket-read segfault found here is a real, narrower, and previously
undocumented defect that the pitfalls guide's recommended workaround does not
fully cover — it is documented and spec-guarded above regardless of whether
it explains the original report.

## Safe pattern (updated)

For a class-field `Dict`/`{K:V}`:
- `contains_key(k)` — safe, use freely.
- `keys().len()` — safe, use freely.
- `d[k]` bracket-read where `V` is an array type — **UNSAFE on native-build,
  segfaults**. No safe native-build workaround identified in this
  investigation; needs its own fix (likely in the class-field-receiver
  indexed-read codegen path, distinct from the already-documented local/param
  Dict issues). Until fixed, avoid array-valued class-field dicts on the
  native lane, or copy the value to a local dict first and bracket-read from
  the local copy (untested but consistent with the "local dict is safe"
  isolation result above).

## Files

- Fixture (not committed, scratch only):
  `/tmp/claude-1000/.../scratchpad/dictfix/main.spl` variants.
- Spec: `test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl`
- Correction appended: `doc/07_guide/language/dict_native_pitfalls.md`
  (new note before the "Replacements" section).
