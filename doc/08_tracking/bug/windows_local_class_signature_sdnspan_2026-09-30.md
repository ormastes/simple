# Windows pure-Simple HIR loses a locally declared SdnSpan type

Status: reproduced in the real 75-module I/O facade closure; precise lowering
site and minimal reproducer are not yet verified. No compiler fix is included.

## Proven evidence

Producer SHA-256:
`cbe4a8df41e14287005e258cf57f8e16bd096dee0c09954b39495446e5ab19cc`.
Consumer source revision: `b8e5068695eb33af29216a83cdf18069a146b73a`, plus the
then-uncommitted native I/O fixture subsequently committed in `5b977b257ca`.
The producer is frozen separately and does not contain the consumer PR by
implication; the entry resolves the PR's source modules from its own worktree.

The positional `native-build` command, with no explicit `--entry`/`--source`,
selected the pure-Simple CompilerDriver. It traversed 75 HIR modules and exited
1 after 40.101448 seconds. Module index 61,
`src/lib/common/sdn/value.spl`, produced exactly four printed fatal diagnostics:
`unresolved type: SdnSpan`. The `hir-fatal-count` row confirms `count=4 shown=4`.
No native fixture executable was run. HIR cache: 0 hits, 75 misses, 74 stores.

Evidence directory:
`D:/dev/simple-windows-stale-facades-20260930/build/native_probe/phase2/cbe4a8df41e14287005e258cf57f8e16bd096dee0c09954b39495446e5ab19cc/facade-entry/`.
Use `build3.started.json`, `build3.result.json`, `build3.stdout.log`, and
`build3.stderr.log` (fatal rows 1344-1348). The earlier `build`/`build2` records
used the embedded Rust route and are not self-hosted qualification.

## Four source annotation locations

The failing module itself declares `pub class SdnSpan` at line 6. Its four
explicit self-type annotations are:

| Source location | Annotation |
| --- | --- |
| `src/lib/common/sdn/value.spl:12:26` | `empty()` return type |
| `src/lib/common/sdn/value.spl:15:45` | `at(line, column)` return type |
| `src/lib/common/sdn/value.spl:18:27` | `merge` parameter `other` |
| `src/lib/common/sdn/value.spl:18:39` | `merge` return type |

These are concrete source locations, not diagnostic spans: the recorded errors
do not identify which lowering invocation produced each row. Their one-to-one
correspondence with the four errors is a hypothesis, not a proven attribution.

## Source-only diagnosis

`module_build.spl` calls `declare_module_symbols` before lowering definitions.
`module_declarations_bootstrap.spl` registers class names before callable
signatures. Its synthetic-impl pass resolves the owner and sets the current
self-type, then invokes `declared_callable_type`. That helper still passes
explicit named parameter/return annotations through ordinary `lower_type`;
supplying an owner context only constructs the implicit receiver type.

Later, `class_declaration_lowering.spl` pushes a class scope and binds the local
class name before lowering class methods. The parser can desugar methods into
synthetic impls, so that later binding cannot establish the earlier signature
pass's lookup state. Inspect owner identity, short-name binding, and the module
scope at signature lowering before changing imports. This module needs no
import of its own `SdnSpan` declaration. Source inspection does not prove whether
the missing binding arises in declaration registration, signature lowering, or
another pass; retain that uncertainty.

## Tiny reproducer proposal (not executed)

Use a class with one field, two static self-returning methods, and an instance
method accepting and returning its owner type:

```simple
pub class SpanProbe:
    value: i64
    static fn empty() -> SpanProbe: SpanProbe(value: 0)
    static fn at(value: i64) -> SpanProbe: SpanProbe(value: value)
    fn merge(self, other: SpanProbe) -> SpanProbe:
        SpanProbe(value: self.value + other.value)

fn main() -> i64:
    val actual = SpanProbe.empty().merge(SpanProbe.at(42))
    if actual.value == 42: 0 else: 1
```

First compile this as a positional entry with the same producer and a distinct
cache. If it passes, preserve that result and introduce a separate provider
module imported through a facade to test closure registration. Do not rerun the
full I/O closure without a concrete compiler change. This lane stopped after
three attempts; these proposals require an independently scoped follow-up.
