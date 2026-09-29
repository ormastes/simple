---
id: native_build_cross_module_trait_only_and_unimported_method_gaps_2026-07-17
status: PARTIAL
severity: medium
discovered: 2026-07-17
discovered_by: lane S49, while building the cross-module probe matrix for #190
  (cross-module trait default-method dispatch on the native path)
related: src/compiler/80.driver/driver_aot_output.spl
related: src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl
related: doc/08_tracking/bug/ (this doc; no prior entry found for either gap)
---

# Two pre-existing, out-of-scope native-build multi-file gaps found while probing #190

## Summary

While building a matrix of two-file `native-build` probes to verify the
#190 fix (cross-module trait default-method dispatch — see the fix commit
touching `register_imported_symbol` in `module_lowering.spl`), two
**separate, pre-existing** gaps surfaced. Neither is caused by, or fixed by,
the #190 change; both are recorded here rather than silently worked around
(both probe cases were redesigned to avoid tripping them).

Both reproduce with `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple
native-build --entry <entry>.spl -o <out> --clean` on a fresh two-file probe;
`bin/simple run` (interpreter) is unaffected in both cases.

## Gap 1 — a trait-only module (no impls, no other functions) fails AOT with "MIR module has no functions"

Probe: `greeter_mod.spl` containing only
`trait Greeter: fn name(self) -> i64 \n fn greet(self) -> i64: return
self.name() + self.name()` (no impl, no free function), imported by an
entry module that implements `Greeter` for a local struct.

```
error: AOT compile error in .greeter_mod: MIR module has no functions
```

Root cause: `driver_native_module_is_export_facade`
(`src/compiler/80.driver/driver_aot_output.spl:125-153`) treats a
zero-function MIR module as a real lowering bug (loud-fail) unless it
qualifies as a "facade" — and the facade predicate explicitly requires
`parsed.traits.len() == 0` (line 150), so ANY module containing only a
trait declaration is excluded from facade treatment, regardless of whether
that trait's default bodies are legitimately consumed elsewhere (injected
into implementing modules' impls, not compiled as standalone functions in
the trait's own module — by design, per #157/#190's injection mechanism).

This is legitimate, not a lowering bug: a trait-only module with no impls
correctly lowers to zero MIR functions. The facade predicate needs a
carve-out for "traits only, no impls, no other real decls" analogous to the
existing extern-only-functions carve-out just above it.

Workaround used for #190's probe matrix: every trait-only probe module got
an extra harmless free function (e.g. `fn greeter_marker() -> i64: return
0`) so its MIR module is non-empty. Real-world trait modules almost always
have more than one declaration, so this is a narrow edge case, but a
single-declaration trait module is valid Simple and should build.

### Gap 1 source fix (2026-07-17)

`driver_native_module_is_export_facade` now accepts a trait declaration as
evidence for a code-free module while retaining every existing exclusion for
functions, data, impls, and other code-bearing declarations. The #190 system
probe no longer adds `greeter190_marker`; its original two-file scenario is the
regression. Execution and SPipe doc generation remain pending under the current
no-runtime-command restriction.

## Gap 2 — calling ANY method (not just a trait default) on a value of an imported struct type, when only the type itself is imported, fails MIR lowering

Probe: entry module does `use .helper_mod.{SomeStruct}` (only the type, not
any function that constructs or uses it) and calls `instance.some_method()`
in its own body, where `SomeStruct`'s method(s) are declared via `impl
SomeStruct: ...` (or `impl Trait for SomeStruct: ...`) entirely inside
`helper_mod.spl`.

```
[mir-lower] WARNING: unresolved method call 'some_method' lowered to const-0 placeholder (silent-null risk, Task #145)
error: MIR lowering error: unresolved method call: some_method
```

Confirmed this is **unrelated to traits**: reproduces identically for a
plain (non-trait) `impl SomeStruct: fn some_method(self) -> i64: ...` with
no trait involved at all. `register_imported_symbol`'s struct arm
(`module_lowering.spl`) does call `register_imported_type_methods`, which
registers a qualified symbol (`{owner_module}.{type}::{method}`) for every
method the imported struct's impl(s) declare (including trait defaults, via
the `impl_.has_trait_` branch at line 487) — so HIR-level symbol resolution
for the call site succeeds. The gap is downstream, at MIR call-site-to-
definition matching across the two independently-lowered modules: the
entry's call to `instance.some_method()` does not resolve to the concrete
MIR function `helper_mod.SomeStruct::some_method` that
`helper_mod.spl`'s own lowering pass produced.

Workaround used for #190's probe matrix ("two importing modules sharing one
trait" case): route the call through a plain cross-module **function**
re-exported from the helper module (e.g. `fn use_b(x: i64) -> i64: return
SomeStruct(v: x).some_method()`) instead of calling the method directly on
an imported-type value from the entry module. Plain cross-module function
calls already work correctly (verified by the existing
`native_cross_module_abi_spec.spl` regression coverage and by #190's own
matrix cases 5/6, which import functions/traits directly rather than typed
values).

### Gap 2 atomic acceptance boundary (2026-07-17)

Do not patch this with a short-name or suffix scan in MIR. Constructor/local
and imported-factory results must retain the defining module plus type owner so
the existing qualified method symbol is selected. Imported trait defaults must
also chase a separately declared trait through a three-module A-trait/B-impl/
C-consumer graph. Acceptance must cover inherent and explicit-trait methods,
same-module and three-module defaults (including default-to-required dispatch),
two modules exporting the same type and method names under aliases, two local
types sharing a method name, typed parameters, constructor locals, and imported
factory returns. Same-name overloads remain separately unsupported and must
fail loudly because parser `Impl.methods` is name-keyed. This remains open; a
single MIR map insertion would be a partial and collision-prone fix.

## Scope note

Neither gap blocks #190 (cross-module trait *default* dispatch specifically
works once the trait and the implementing type are directly imported by the
same module, or the type crosses a module boundary via a plain function
rather than a bare type import). Gap 2 remains open rather than silently
working around the discovered defect.
