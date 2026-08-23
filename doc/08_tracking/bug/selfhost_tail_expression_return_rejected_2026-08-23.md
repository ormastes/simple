# Self-hosted compiler rejects a tail-expression return that the seed accepts (D3)

- Date: 2026-08-23
- Severity: HIGH (seed-passes / self-hosted-fails -- the class that matters for self-hosting)
- Status: OPEN (filed, not fixed)
- Area: MIR lowering return analysis (`E-SFFI-016`)

## Reproducer (VERIFIED)

`d3.spl`:

```
fn main() -> i64:
    println("hi")
    0
```

Rust seed (`bin/simple run d3.spl`):

```
rc=0
hi
```

Self-hosted stage2 (`/mnt/data/bootstrap-run28/stage2/x86_64-unknown-linux-gnu/simple`,
132,930,184 bytes, commit `9c5e2dad378`):

```
SIMPLE_HIR_CACHE=0 ./stage2 native-build d3.spl
rc=1
[ERROR] MIR error: MIR lowering error: E-SFFI-016: missing return in non-unit function 'main'
error: in-process native-build: MIR lowering error: E-SFFI-016: missing return in non-unit function 'main'
```

Exit statuses read directly into a variable, not through a pipe.

## Analysis

A bare trailing expression is a valid return in Simple -- the language uses it
throughout (`_compile_frozen_module_capsule` itself ends in `Ok(object_path)`,
and `FrozenNativeModuleCapsuleBatchV1.find` ends in a bare `Item(...)`
constructor). The seed implements this; the self-hosted return analysis does not
recognise a bare literal tail expression as satisfying a non-unit return type.

Writing the same function with an explicit `return 0` gets past this check (and
then hits the separate AOT SEGV tracked in
`selfhost_struct_method_hijacked_by_string_arm_2026-08-23.md`), which isolates
the defect to the return-presence analysis rather than to codegen.

Not yet determined (ASSUMED, needs confirmation): whether the analysis fails for
all bare tail expressions or only for a bare literal. `Ok(...)`-shaped tails
evidently do reach lowering, so a literal-specific gap is the more likely shape.

## Why it matters

This is a seed-passes / self-hosted-fails divergence. Every such divergence is a
latent bootstrap break: source that compiles today under the seed can stop
compiling the moment the self-hosted binary becomes the default tool.
