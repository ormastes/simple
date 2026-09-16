# Seed divergences hit while making the sspec scorer runnable (2026-09-05)

Fresh seed rebuilt from current source (`cargo build --profile bootstrap -p
simple-driver -p simple-native-all`, 2026-09-05) still diverges from the
pure-Simple toolchain on two constructs the stdlib and `src/app/**` rely on.

## 1. No-arg `.split()` is not whitespace-split on the seed

- `"a b c".split()` on the seed returns an **empty array** (len 0), silently.
- On a chained receiver (`s.lower().split()`) it errors instead:
  `Runtime error: Function 'str.split' not found` — this killed
  `sspec-maintain` scoring runs (`analyzer.spl:53`, `scaffold.spl:28`,
  `source_facts.spl:202,246,557` all used the no-arg form).
- The pure-Simple toolchain treats no-arg `.split()` as whitespace
  tokenization (current `src/**` depends on it).

## 2. Unannotated return + implicit trailing expression returns nil on the seed

`std.text_advanced.split_whitespace` was
`fn split_whitespace(text: text):` with a trailing bare `result` expression —
on the seed every call returned **nil** (silently; `print parts.len()` printed
nothing). The pure-Simple toolchain honors the trailing-expression return.
Fixed in the same session by making it explicit:
`-> [text]` + `typed var` + `return result`
(`src/lib/common/text_advanced.spl:59`). That style (explicit return type +
explicit return) should be preferred everywhere both toolchains run a function.

## Mitigations landed (pure Simple, no seed change)

- `split_whitespace` made explicit (above).
- The five no-arg `.split()` sites in `src/app/sspec_maintain/` were switched
  to imported free-function `split_whitespace(...)` calls — method-position
  `x.split_whitespace()` ALSO fails on the seed (`Function 'str.split_whitespace'
  not found`): the seed resolves text-receiver method calls only against its
  builtin registry, not stdlib free functions (no UFCS).

## Proper fix (seed side, unblocked owner)

- Support no-arg `str.split` as whitespace split in the seed runtime.
- Support implicit trailing-expression returns for unannotated functions, or
  reject them at compile time instead of silently returning nil.
