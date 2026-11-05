# `for` loop variable does not shadow a same-named module-namespace alias

Date: 2026-08-18
Status: OPEN (compiler defect; worked around in library code)
Component: Rust seed compiler / interpreter name resolution

## Symptom

`test/00_formal_verification/compiler/verification_diagnostics_spec.spl` failed:

```
✗ collects and formats diagnostics
  semantic: method `format` not found on type `dict` (receiver value:
  {Severity: <enum:Severity>, ... Span: <constructor:Span>, Span__empt...)
```

The receiver is the *module namespace dict*, not the loop element.

## Cause

`src/compiler_rust/lib/std/src/verification/lean/verification_diagnostics.spl`
contained:

```
    fn format_all() -> List<text>:
        var result: List<text> = []
        for diag in self.diagnostics:
            result = result + [diag.format()]
        result
```

The spec imports that module as `use ... as diag`. Inside the callee the
for-loop binding `diag` loses to the module-alias binding of the same name, so
`diag.format()` dispatches on the namespace dict.

## Minimal reproduction (compiler-level, independent of this module)

```
# m.spl
class Box:
    v: i32
    static fn new(v: i32) -> Box: Box(v)
    fn show() -> text: "{self.v}"
class Holder:
    items: List<Box>
    static fn new() -> Holder: Holder([])
    me push(b: Box): self.items = self.items + [b]
    fn show_all() -> List<text>:
        var result: List<text> = []
        for m in self.items:            # loop var named like the spec's alias
            result = result + [m.show()]
        result

# r_spec.spl
use tmp_repro.m as m
...
```

Result: `semantic: method `show` not found on type `dict` (receiver value:
{Box: <constructor:Box>, ...})`.

## Current mitigation

The loop variable in `format_all` was renamed to `entry`. This is a workaround,
not a fix: any `for <name> in ...` whose `<name>` collides with an importer's
module alias is still mis-resolved.

## Real fix (TODO)

Make the `for` binding shadow module-namespace bindings in the interpreter /
JIT scope chain, and add a language-level spec asserting loop-variable shadowing
precedence over imported module aliases.

## Note 2026-11-05 (related)

Same class, spec-lane reassignment: in a block body, `var input = ...; input = f(...)` with a
module named `input` imported dropped the local, because `module_global_target`
(`interpreter_call/block_execution.rs`) returned the `Legacy` global target before consulting
`env.is_local`. Locals now win first. Regression: `test/01_unit/compiler/interpreter/local_shadows_builtin_input_spec.spl`.

## Not reproducible at current source — 2026-11-05

The doc's minimal reproducer shape was rebuilt at current release/1.0.0 and
run on an aarch64 Linux host with the deployed seed, on BOTH lanes: a
consumer module aliasing a provider as `m` (`use m.{Box}`), with a for-loop
variable named `m` whose body calls `m.show()` on the element. Expected
(filed behaviour): dispatch on the namespace dict ("method `show` not found
on type `dict`"). Observed: `box1` / `box2` on BOTH the JIT and interpreter
lanes — the loop binding shadows the module alias, `m.show()` dispatches on
the Box element. The 2026-11-05 locals-win resolution change
(module_global_target consulting env.is_local first, regression
local_shadows_builtin_input_spec.spl) appears to cover the for-binding case
as well; no separate loop-scope fix was found in history.
