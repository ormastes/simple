# HIR aliases lose the underlying receiver representation

Date: 2026-09-29. Status: isolated source correction prepared; changed-code
native validation pending. No bootstrap phase qualification is claimed.

## Observed failure

The diagnostic fixtures were based on
`240d9509bd4492a4850db97d1501f0ddcef2ff6b`. The actual frozen self-hosted
producer came from source `5da86869df060ad4c1b87abfd2384f8d2a761e3a`, SHA-256
`a45ede92cdbb972d26369ccaa6c42960ec2fca64e560e106ec7a0ca2c8e3747b`.
Each fixture ran once with LLVM 23.1.2, one native worker, strict unresolved
stub fallback disabled, inventory cold initialization, and a 60 second wall
timeout. RSS was measured; no RSS, VM, or data cap was imposed.

Evidence root: `D:/dev/simple-logic-no-rss-20260929/.logic-no-rss/`.

| Fixture | Actual result | Compile seconds / max RSS KiB | Unique attempt under evidence/ |
|---|---|---|---|
| `alias-field.spl` | Compile 1: unresolved `contains_key` and `contains`; no executable run | 0.82 / 234016 | `alias-field/attempt-20260929T035053Z-337264` |
| `plain-field.spl` | Compile 0, executable 0, exact stdout `plain-field:PASS` | 22.16 / 250196 | `plain-field/attempt-20260929T035106Z-337615` |
| `text-bool.spl` | Compile 1: unresolved `contains`; no executable run | 0.68 / 234116 | `text-bool/attempt-20260929T035117Z-338065` |

The first two fixtures exercise the same dictionary/text values and unrelated
`Decoy` methods. The failing holder uses a dictionary alias chain and a text
alias; the passing holder uses the underlying types directly. The text/bool
fixture cannot qualify its bool behavior because compilation fails first.
These failures completed before timeout and do not establish a memory failure.

## Source cause

Local aliases were registered as `SymbolKind.TypeAlias` with a nil type target
in `module_declarations_bootstrap.spl`. Compound and generic imported aliases
were similarly registered without targets in `module_import_registration.spl`.
`lower_named_kind` returned a nominal `HirTypeKind.Named` for these symbols.
MIR's dictionary/text builtin dispatch therefore could not see the underlying
receiver shape. This source trace explains the observed alias/plain difference;
fresh execution is required to establish the correction's native behavior.

## Correction and contracts

The lowerer retains alias parser templates keyed by actual module-local
`SymbolId`. A compact ID-indexed position table gives constant-time lookup
for alias and ordinary nominal type uses. `begin_module` clears the templates
and positions together with the symbol table.

Expansion lowers the target to its underlying HIR representation. It retains
actual generic arguments, allows defaults to refer to earlier formals, and
detects recursive aliases by active symbol ID. Expansion restores its argument,
owner, scope, and recursion frames. Local aliases capture their declaration
scope; imported aliases materialize and resolve their owner's qualified type
dependencies, including default dependencies. A consumer's same-named type
cannot supply an unknown imported target.

The existing imported nominal forwarding path remains for a truly bare named
target. Compound targets and targets with arguments use templates; the payload
identity predicate uses the same forwarding condition. Imported field and
signature projections normalize aliases and retain arguments, including an
array element such as `Box<i64>` when `Box<T=text>` has a default.

## Regression and validation boundary

`test/01_unit/compiler/hir/type_alias_representation_spec.spl` asserts parsed
local chains and primitive aliases, generic composite substitution, defaults
and arity errors, cycle cleanup, declaration-scope shadowing, imported owner
collisions, unknown-owner refusal, reset isolation, and generic array field and
return projection. Generic templates in the HIR tests are constructed as
parser records; those assertions do not claim generic alias parser coverage.

The regression spec is unexecuted at source review. Static review found no
remaining blocking defect after correcting the initial linear alias lookup and
both array projections that dropped actual arguments. Native field/signature
execution remains necessary because the existing projection code documents
staged aggregate ABI hazards. The unchanged alias/text/Decoy fixtures must be
compiled and run with a fresh corrected producer before merge. The already
passing plain control should not be rerun against unchanged inputs.
