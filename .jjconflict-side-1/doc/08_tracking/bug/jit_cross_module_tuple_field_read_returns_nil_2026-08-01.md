# JIT: cross-module tuple `.0` read returns nil

**Status:** OPEN — found 2026-08-01 while fixing
`common_encoding_yaml_broken_cross_submodule_import_2026-07-20`.

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
