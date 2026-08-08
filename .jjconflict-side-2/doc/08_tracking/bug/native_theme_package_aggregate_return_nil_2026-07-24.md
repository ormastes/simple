# Native theme-package aggregate return becomes nil

Status: open compiler/runtime bug; production startup bypasses the unsafe
boundary with the generated immutable `ThemeRenderSnapshot`.

## Reproduction

An exact-current pure-Simple Stage 3 driver successfully native-builds
`src/app/cli/theme_sync.spl` with the current host runtime providers. Running
the resulting native executable as:

```sh
build/aetheric-theme-sync-native compile-to-spl \
  --theme=aetheric_dark \
  --out=src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl
```

fails with `runtime error: field access on nil receiver`.

The hosted WM failed at the same boundary when
`install_default_host_wm_theme()` read
`load_default_theme_package().snapshot`. Extracting the returned package to an
owner-local value did not change the fault, so this is not a temporary-value
lifetime issue.

## Impact

- Native startup must not call `load_theme_package()` and then project the
  returned aggregate class.
- Hosted WM and Web production consumers enforce that boundary: hosted startup
  uses active/generated immutable snapshots, while Web receives only owner-
  projected scalar CSS/fingerprint text from the package module.
- Native theme compiler execution cannot currently regenerate the tracked
  snapshot.
- Interpreted development tooling can still compile the folder package; the
  output remains the immutable production input for hosted and bare-metal
  startup.

## Required root fix

Add a focused native regression that returns the complete `ThemePackage`
aggregate across a module boundary and reads `snapshot`, `token_map`, and
`widget_css_by_name`. Trace HIR/MIR result ownership, class discriminants, and
native return ABI until all fields remain non-nil. Remove the generated
snapshot startup bypass only after that regression and the host launch both
pass.

## Owner-boundary diagnosis

The source declarations and package construction agree; this is not a theme
schema or constructor mismatch. `load_theme_package` constructs a complete
`ResolvedThemePackage` and returns the named local `pkg`, while
`load_default_theme_package` forwards that result across a module boundary.
Named class values lower as `MirTypeKind.Struct`, but the native call/return
path transports the result through the generic pointer/i64 ABI. Existing
return-type recovery already has special handling for lost declared result
types, so the first boundary to pin is MIR return/call-destination provenance,
before changing Cranelift ABI code.

The generated `aetheric_dark_theme_render_snapshot()` startup path is a
fail-closed production bypass, not proof that this bug is fixed: it returns a
direct aggregate literal and does not exercise the named-local package return
or the cross-module wrapper.

The minimal regression matrix must use two modules and project all three
nontrivial fields (`snapshot`, `token_map`, and `widget_css_by_name`) after:

1. a bare named-local tail expression;
2. an explicit `return pkg`;
3. a direct constructor tail; and
4. `load_default_theme_package()` forwarding the package result.

Inspect the HIR/MIR destination type and `Ret` operand in each row. A source
workaround that defaults nil fields, adds raw runtime aliases, or further
special-cases theme startup is explicitly rejected.
