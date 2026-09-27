# JIT: class instances alias instead of copying (violates value-type ruling)
## Open 2026-09-27

- Date: 2026-09-27
- Severity: high (engine divergence: the same program prints different results
  under `SIMPLE_EXECUTION_MODE=interpreter` and `=jit`)
- Found during: retargeting `test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl`
  to the owner's value-semantics ruling.

## Ruling
Owner, 2026-09-27: classes are value types
(`doc/07_guide/language/capability_library_authoring.md:33` — "`val b = a`
copies"). A mutation through a copy must not reach the original; it persists
only through an explicit write-back.

## Symptom
Probe `test/01_unit/compiler/interpreter/probe_dict_class_value_identity.spl`,
Rust seed built from `origin/main` 6952f73f686 (Windows x86_64):

- `SIMPLE_EXECUTION_MODE=interpreter`: `DICT_CLASS_VALUE PROBE: ALL PASS` (16/16).
- `SIMPLE_EXECUTION_MODE=jit`: `FAILURES=8`. Every "original unchanged" check
  fails because the JIT shares the instance:

```
FAIL dict_get_original_unchanged got=5 want=0
FAIL dict_text_key_original_unchanged got=99 want=10
FAIL callee_copy_mutated_again got=2 want=1
FAIL callee_field_dict_hits_unchanged got=2 want=0
FAIL callee_field_dict_last_unchanged got=seen want=none
FAIL array_elem_original_unchanged got=42 want=1
FAIL two_handles_second_independent got=77 want=0
FAIL val_assign_original_unchanged got=4 want=3
```

The last line is the plainest form: `val a = Cache(hits: 3, ...)`,
`val b = a`, `b.hits = 4` leaves `a.hits == 4` under the JIT.

## Not yet checked
Whether native (LLVM/Cranelift AOT) codegen shares the JIT behaviour. If it
does, the fix is a codegen-wide copy-on-assign/copy-on-read change, with a
large blast radius (every site that currently relies on aliasing, e.g. the
`caches.set(id, cache)` write-backs this record's sibling
`interp_dict_class_value_copy_on_get_mutation_loss_2026-07-06.md` documents,
would keep working; sites relying on aliasing without a write-back would break).

## Regression gate
`dict_class_value_identity_spec.spl` asserts the ruling on the interpreter
engine only. When this is fixed, add the JIT run back to that spec.
