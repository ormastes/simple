# REQ-002 shared engine fixtures

Authored fixtures only; all execution and engine admission are pending.
No generated PASS output or completed REQ-002 claim is made.

The existing `scripts/check/check_engine_differential.spl` discovers these four
programs under `test/fixtures/engine_differential/` without a new runner:

| Fixture suffix after `collection_req002_` | Independent literal oracle |
|---|---|
| `map_filter_capture.spl` | Captured offset maps to `[10,8,10,9]`; filtering retains both tens; text lengths `[1,3,2]`; escaped closure retains factory-local prefix (`owned:a`, `owned:bbb`, `owned:cc`); empty stays empty; input unchanged |
| `flatmap_empty_order.spl` | Runtime flat_map and actual library flatten each produce `[2,12,1,11,2,12]`, including empty expansion |
| `any_all_shortcircuit.spl` | Builtin and library any/all stop after two callbacks; empty yields false/true with zero callbacks |
| `dict_struct_overwrite.spl` | Two keys after overwrite; independent present/absent probes; exact struct fields preserved |

These supplement existing `closure_runtime_facing.spl`, `closure_capture_list.spl`
and the Dict differential guard. Algorithms are not copied into test helpers.
Each main returns nonzero silently on a wrong semantic result and emits its sole
fixed `REQ002|...` marker only after every check succeeds. The marker text in the
source is the same immutable oracle for every lane; disagreement alone is not
the oracle. Fixture source and binary digests must accompany eventual results.

## Same program across modes and compiler generations

Use the existing `DIFF_FILTER=collection_req002_` discovery selector. Interpreter
and JIT use existing `DIFF_LANES=interpret,jit`; LLVM is the actual `native` build
lane, never an invented execution-mode environment value. Self-hosted and
bootstrap-produced compilers are binary provenance, not additional mode strings.
Keep the exact same four sources and markers for both generations. Bootstrap
does not authorize Rust-seed tests: only admitted pure-Simple artifacts may run
verification; the Rust seed remains bootstrap-only. No command was run here.

## Existing harness limitations that block certification

Strict no-fallback execution is required before accepting parity. The canonical
runner currently pins engine names but `run_interpreted` does not enforce
`SIMPLE_JIT_STRICT`, collect a positive JIT witness, or check child exit status.
`run_native` explicitly supplies `SIMPLE_SCV_FREEZE_FALLBACK=1` and also ignores
the final program exit status. It compares nonempty normalized stdout rather
than enforcing an expected-marker file. Thus its AGREE verdict alone cannot
certify these fixtures, identical runtime diagnostics, or actual engine identity.
Future admitted evidence must require exact markers, zero exit, engine provenance,
and no fallback; this test-only change does not authorize admission bypasses or
modify runner behavior. All-whitespace differences are outside its comparison.
The SCV knob relaxes source-inventory snapshot admission; it is distinct from
execution-engine fallback and does not by itself mean native code was interpreted.

No expected-missing-runtime-symbol facility was found in this harness: such a
fixture would be reported as a lane error, not a verified negative. That negative
gate remains explicitly missing. Native admission, optional struct payload ABI,
closure capture, and callback mutation are unvalidated until real runs occur.
