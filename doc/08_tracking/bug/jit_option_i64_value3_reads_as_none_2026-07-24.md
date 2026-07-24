# JIT: `Option<i64>` holding value `3` reads as `None` (tag-box niche collision)

**Date:** 2026-07-24
**Severity:** High — a JIT correctness bug. Any JIT-compiled code that stores the
integer `3` in an `Option<i64>` silently gets `None`. Confirmed to break the test
runner (below); the blast radius is every `Option<i64>` in JIT-compiled code.
**Layer:** JIT / native tag-box lowering (`hir/lower/expr`), NOT the interpreter.

## Minimal repro

```simple
fn main():
    val b2: i64? = 2
    val b3: i64? = 3
    val b4: i64? = 4
    if b2 == nil: print("b2=NIL") else: print("b2=SOME")   # SOME (correct)
    if b3 == nil: print("b3=NIL") else: print("b3=SOME")   # NIL  (WRONG — should be SOME)
    if b4 == nil: print("b4=NIL") else: print("b4=SOME")   # SOME (correct)
```

- `val b: i64? = 3` then `print(b)` prints **`nil`** — the value is *stored* as
  None, so it is a coercion/encoding bug, not a comparison bug.
- Swept `-2..12`: **only `3`** reads as None. Every other value is fine.

## It is JIT-only (interpreter is correct)

| Mode | `val b: i64? = 3` | `"ab example".index_of("example")` (match @ offset 3) |
|------|---|---|
| default (JIT) | **NIL** | **nil** |
| `SIMPLE_EXECUTION_MODE=interpreter` | SOME | SOME 3 |

Forcing the interpreter fixes both. So the defect is in the JIT/native tag-box
encoding, where the `Option<i64>` None discriminant collides with the tag-boxed
form of the integer `3`. This is the documented BoxInt `(v << 3) | TAG_INT`
tag-box class — see `hir/lower/expr/mod.rs:942` and memory
`project_stage4_wall_and_hardening_2026-07-04` ("BoxInt <<3 mangles ... thru ANY").

## Present in both binaries (real bug, on origin — not a bad local build)

Identical failure on the deployed `bin/release/.../simple` (48 MB, 2026-07-24)
**and** the Rust seed `src/compiler_rust/target/bootstrap/simple` (31 MB,
2026-07-22). So it is committed seed/JIT source, not a stale artifact.

## Downstream impact that surfaced this — test-runner false negatives

`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` parses each child
spec's `"N examples, M failures"` summary via `extract_number_before`, which does
`s.index_of("example")`. `index_of` returns the match offset as `Option<i64>`.
When the summary is `"10 examples…"` … `"99 examples…"`, `"example"` lands at byte
offset **3** → `Some(3)` → reads as `None` → `-1` → the count is unparseable →
`make_result_from_output` returns *"no parseable pass/fail summary in test output;
refusing synthetic pass"* → the spec is falsely marked FAILED.

- **9-example spec** (offset 2) → PASS. **10–99 examples** (offset 3) → false
  FAIL. **100+ examples** (offset 4) → PASS again. Boundary swept & confirmed
  (n=9 PASS, n=10 FAIL, verified up to n=20; `"100 examples"` re-passes).
- Real specs hit by this: `loader_shared_core_spec` (20 ex),
  `spec_constants_contract_spec`, `utf8_validation_spec` — all genuinely GREEN
  (`20 examples, 0 failures` under `simple run`) but reported FAILED under
  `simple test`.

## No runtime stopgap

`SIMPLE_EXECUTION_MODE=interpreter` does **not** rescue `simple test`: the test
runner itself is precompiled into the binary with the buggy encoding, and the env
var only affects how child specs execute, not the baked-in parent parser. The fix
requires correcting the JIT tag-box/niche encoding and rebuilding.

## Fix direction

In the JIT tag-box lowering, ensure the `Option<i64>` (and generally `Option<T>`
over a niche-less payload) None discriminant cannot collide with any tag-boxed
payload value — e.g. reserve a niche the payload space cannot produce, or box
`None` distinctly from `(3 << 3)|TAG_INT`'s neighbourhood. Verify with the
`-2..12` sweep above plus the `index_of` offset-3 case; then re-run the three
affected specs under `simple test` (not `run`).

## Supersedes

Retracts `named_arg_self_field_value_parse_regression_2026-07-24.md` — that
analysis blamed a `self.field` named-arg parse hint, which is a harmless
Info-level style diagnostic and a **red herring** (specs with ≤9 `self.field`
uses and ≥50 uses both pass; the real discriminator is example *count* ≥ 10).
