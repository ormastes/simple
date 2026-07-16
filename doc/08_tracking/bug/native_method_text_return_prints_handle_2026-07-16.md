# Native: method returning text prints raw handle integer

**Status (2026-07-16):** open. Reproduced at main tip c8f4b62261a (after the
rt_dict/rt_tuple extern-migration revert). Found while verifying
`native_method_cleanup_global_misresolution_2026-07-13` (lane method_cleanup).

A struct impl method returning `text` builds and dispatches correctly under
`native-build --entry`, but `print()` of the returned value emits a raw
runtime-handle integer instead of the string content.

Repro (dual-backend protocol):

```simple
struct Widget:
    name: text

impl Widget:
    fn describe(self) -> text:
        return "widget:" + self.name

fn main() -> i64:
    val w = Widget(name: "w1")
    print(w.describe())
    return 0
```

- Oracle (`env -u SIMPLE_BOOTSTRAP bin/simple run`): `widget:w1`
- Native (`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry ... --clean`
  then run): a raw integer such as `99089996469537` (varies per run), rc 0.

Not a regression from the 2026-07-15/16 churn: reproduces identically at
ca1e18c1744^ (pre "wip(os): checkpoint memory leveling native verification")
and at c8f4b62261a. Same-shaped programs whose methods return `i64` have full
parity (see `method_owner_dispatch` in
`scripts/check/check-native-seed-parity.shs`), so this is a text-return
decode/print gap on the method-call result path, not a dispatch defect. Likely
area: method-call result typing in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (result local
not registered as text/runtime-string, so `print` lowers to the integer
variant).
