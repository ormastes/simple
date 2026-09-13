# JIT: cross-module tuple `.0` read returns nil

**Status:** CLOSED (2026-09-12) — not reproducible; see "Re-check 2026-09-12" at the end. (Was: OPEN — found 2026-08-01 while fixing
`common_encoding_yaml_broken_cross_submodule_import_2026-07-20`.)

**Engine:** Cranelift JIT (`simple run` path). Not observed on the tree-walk
interpreter.

## Symptom

A tuple built by a function in ANOTHER module reads back `nil` through
positional field access, while a predicate defined alongside the constructor
reads the same tuple correctly:

```
# src/lib/common/yaml/types.spl
fn yaml_string(content: text):
    ("string", content)

fn is_yaml_scalar(v: any) -> bool:
    val t = _yaml_tag(v)
    t == "null" or t == "boolean" or t == "number" or t == "string"
```

```
yaml_string("hi").0        # -> nil     (WRONG, expected "string")
is_yaml_scalar(yaml_string("hi"))   # -> true   (correct)
```

The value is intact — only the cross-module positional read is wrong. An
accessor compiled in the tuple's own module sees the right data.

## Why it matters

This is the silent-wrong-result class, not a crash. A caller that branches on
`v.0 == "string"` takes the false branch forever and produces empty output with
no diagnostic. That is exactly how the yaml defect above stayed hidden: the dead
`== "scalar"` compare and this read defect would BOTH have to be fixed to see a
correct result, so fixing either one alone still looked broken.

## Not yet established

- Whether it is specific to tuples returned by value from another module, or to
  any aggregate crossing a module boundary.
- Whether the index matters (`.0` vs `.1`).
- Whether the whole-program native path shares the defect, or only `run`.

Recorded rather than investigated: it was out of scope for the yaml lane, and
guessing at the boundary would be worse than stating the measured case.

## Workaround

Use a predicate or accessor defined in the same module as the constructor
(`is_yaml_scalar(v)` rather than `v.0 == ...`). The yaml fix takes this route
and is immune to the defect as a side effect.

## Re-verified 2026-08-09 — still reproduces, still architectural (Rust seed)

Fresh minimal repro (2-file, no yaml involved), run against
`bin/release/x86_64-unknown-linux-gnu/simple` (seed banner confirmed):

```simple
# tupmod_a.spl
fn make_tup():
    ("string", "hi")

# tupmod_main.spl
use tupmod_a.{make_tup}

fn main():
    val v = make_tup()
    print("field0={v.0}")
```

`bin/simple run tupmod_main.spl` -> `field0=nil` (expected `"string"`).
Confirms the defect is general to any cross-module tuple constructor, not
specific to yaml's `yaml_string`. Root cause remains the Cranelift JIT
codegen path (`src/compiler_rust/compiler/src/codegen/**`) — out of scope for
a pure-Simple (`.spl`) fix; leaving OPEN. No regression risk introduced since
no source under `src/` was changed for this bug.

## Re-investigated 2026-08-10 (correcting a prior blanket-claim mislabel)

A prior pass in this session had mass-relabeled this doc using the incorrect
claim "the JIT is implemented entirely under `src/compiler_rust/**`,
off-limits" as a blanket rule. Checked specifically for THIS bug:

- Re-reproduced fresh with the doc's exact 2-file minimal repro
  (`tupmod_a.spl` / `tupmod_main.spl`) against the currently deployed binary
  (`bin/release/x86_64-unknown-linux-gnu/simple`, confirmed via
  `bin/simple --version` to be the Rust seed): `bin/simple run
  tupmod_main.spl` -> `field0=nil`, still wrong, matching every prior
  measurement in this doc exactly.
- This is `bin/simple run`, i.e. the Cranelift JIT path, which the doc
  already correctly scopes to `src/compiler_rust/compiler/src/codegen/**`.
  There is no tree-walk-interpreter component to this bug at all (the doc's
  own header states "Not observed on the tree-walk interpreter"), so the
  "interpreter lives in pure Simple" correction does not even apply here —
  this bug was never attributed to the interpreter in the first place, only
  to Cranelift JIT codegen, which genuinely is Rust-only
  (`src/compiler_rust/compiler/src/codegen/`; there is no self-hosted
  Cranelift/native codegen backend under `src/compiler/` that lowers to
  machine code the same way — the closest pure-Simple analog,
  `src/compiler/50.mir/`, only produces MIR, not native codegen, and per
  `reference_pure_simple_codegen_lacks_text_ptr_len_abi` and related memory
  notes the pure-Simple native pipeline is a materially different,
  less-complete path).

Conclusion: this doc's classification was already correctly scoped to
Cranelift-specific Rust codegen and was not meaningfully affected by the
blanket-claim error (which was about the *interpreter*, not the JIT). Status
unchanged: **OPEN — ARCHITECTURAL (Cranelift JIT codegen,
`src/compiler_rust/compiler/src/codegen/**`, re-confirmed by fresh repro
2026-08-10, unchanged output `field0=nil`)**.

## Re-check 2026-09-12

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).

The record's own reproducer, importing the real `std.common.yaml.types`:

```
$ SIMPLE_EXECUTION_MODE=jit         bin/simple run tuple.spl
f0=string f1=hi scalar=true isstr=true
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run tuple.spl
f0=string f1=hi scalar=true isstr=true
```

`yaml_string("hi").0` is `"string"`, not `nil`. **Not reproducible** — status
CLOSED.

Two of the three "Not yet established" questions are now answered on this seed:
the index does **not** matter (both `.0` and `.1` read correctly), and the
same-module predicate and the cross-module positional read agree. The third —
whether the whole-program native path shares the defect — is still unmeasured;
this re-check covers `run` only, on both engines.

Regression guard: `test/01_unit/bugs/jit_cross_module_tuple_field_read_spec.spl`
(8 examples). Each cross-module positional read is paired with the same-module
predicate over the same tuple. That pairing is the point: the predicates stayed
correct throughout the defect, so a guard built only from predicates would be
vacuous, and pairing them makes a future failure attributable to the read rather
than to the constructor. The `v.0 == "string"` caller-branch shape — the one
that took the false branch forever — is pinned in both polarities.

```
SPEC FILE VERDICT: test/01_unit/bugs/jit_cross_module_tuple_field_read_spec.spl outcome=OK declared>=8 executed=8 passed=8 failed=0 skipped=0 dropped=0
```

Non-vacuity proof: substituting the documented buggy answers (`v.0` is `nil`,
the tag comparison is false) turns the file RED —
`outcome=ERROR declared>=8 executed=8 passed=6 failed=2 skipped=0 dropped=0`.
