# Call arguments bypass contextual unsafe block parsing

- id: parser_unsafe_call_argument_context_2026-10-30
- severity: P1 (bootstrap compilation blocker)
- status: parser source fix authored; bootstrap workaround ACTIVE pending exact
  producer qualification

## Evidence and provenance

Run `41042783702`, Linux job `124024288088`, consumed source
`0b10ef7c77838712d4fe4a24d96e88167097ce1e` and failed in
`lockless_map_i64.spl:63:39` at the colon after an unsafe capability header.
The resumed producer originated from Phase1 run `40157771919`, built
from `b60d965abacfa8d21056b9344409aa2db61914ef` (SHA256
`e05b9162248105144b99ae85b1a88431e0983bcf0ac0e9a63ebc1307efe0d6bb`). Both
the current and old parser primary recognize contextual `unsafe` and `danger`;
the source bug is in call-argument dispatch, not in the contextual primary.

## Root cause and repair owner

`parse_call_arg_raw` in `src/compiler/10.frontend/core/parser_expr.spl`
consumes every identifier through a fast path. For identifiers spelled
`unsafe` or `danger`, this bypasses `parse_expr` and its existing contextual
primary probe, so `Ok(unsafe(capabilities: [ffi]): expression)` is treated as
an ordinary call and the following colon is rejected. The repair owner is
argument dispatch in `parse_call_arg_raw`: snapshot lexer and parser tokens,
look ahead only for `(` after these two identifier spellings, restore both
snapshots, then route that original stream through `parse_expr`. Named labels,
ordinary calls, and the primary's existing unsafe grammar remain authoritative.

## Compatibility workaround and authored evidence

The old Phase1 producer cannot consume the newly repaired call-argument
syntax while compiling its own source. In
`src/lib/nogc_async_mut/concurrent/lockless_map_i64.spl`, the affected
expression is kept as an explicit local:

```simple
val reference = unsafe(capabilities: [ffi]): async_ref_from_core_i64(self._scope, entry)
Ok(reference)
```

This preserves the `@unsafe` annotation, unsafe body, and `ffi` capability.
The source-compatibility workaround is marked at that binding and remains
ACTIVE until the removal gate below is satisfied.

`test/01_unit/compiler/frontend/unsafe_call_argument_parser_spec.spl` authors
real flat-AST cases for positional constructor calls, nested ordinary and
method-call arguments, named arguments, ordinary `unsafe`/`danger` identifiers
and calls, named labels, malformed headers, invalid capability payloads, and
the bootstrap local binding. The tests are **UNRUN**; no RED or GREEN result is
claimed. Database reconciliation is pending because no qualified CLI is
available. No compiler, test, seed, or native-build result is claimed.

## Workaround removal gate

Remove the local binding workaround only after an exact admitted producer
includes this argument-dispatch repair (or a reviewed equivalent), the
original-form parser AST regressions pass on that producer, the real map
compilation succeeds, and required verification passes. Source ancestry or a
stage label alone is insufficient. A compatible cross-source producer is
acceptable when the required feature and ABI compatibility are proven; this
bug does not impose a global source-equality admission rule.
