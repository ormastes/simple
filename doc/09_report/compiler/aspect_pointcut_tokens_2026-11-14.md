# Shared pointcut token prerequisite — 2026-11-14

Scope: first P0 accessor prerequisite. Shared lexical scanning and Boolean validation now feed compiler/interpreter pointcut matching; selector cache schema is version 2. Compact and parser-serialized qualified/glob names agree. Simple `#` line comments are removed lexically. Unsupported `call`, `get`, `set`, `init` and `effect` remain rejected. Legacy non-selector cache normalization is preserved, including `@`, `module:` and `effect:` payloads containing parentheses or comment markers. This cache-dispatch guard has source review and repository regression assertions; those SSpec assertions were not executed in the extracted native probe.

Named-aspect ownership, HIR owner serialization/codec regeneration, typed field consumers, `within`/`attr` semantic matching and full accessor generation are not completed by this patch.

## Executed evidence

- Producer: admitted pure-Simple phase 2, SHA256 `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
- Provider: explicit `--runtime-bundle core-c`, native AArch64 host.
- Isolated committed Git fixture: `/tmp/aspect-tokenizer-native-20261114`, entry `src/main.spl`; explicit private cache `cache-cycle2`; one compiler thread; compile bounded to 60 seconds, execution to 10 seconds.
- Compile exit 0; execution exit 0; **57 PASS assertions**. Includes both matchers against independent expected results, compact/serialized spelling, dotted names/globs, Boolean precedence, rejected call/get forms, trailing text/operator, unsupported `&&`, comments and lexical canonical identity.
- Fixture contains the exact parser owner and complete pointcut matcher function blocks from both compiler and interpreter, excluding unrelated module imports. This is extracted-production native evidence, not full-module linkage, SSpec runner, full compiler or Phase-3 qualification.
- Retained logs: `compile2.log`, `run2.log`, extraction note, fixture Git source and native binary in that fixture directory.

Fixture source SHA256: `f5cc6f64beca1e17c0dc993007e52ec118ad483151611375e4283ed9138a35a4`. Native binary SHA256: `89dd4a071a3a9e77f37fe325f1f7bdc0677cf673970773bbd623d03990b22565`.

Repository regressions were added to the existing predicate parser, cross-matcher parity probe and AOP cache specs. The general SSpec runner and full compiler/lib/MCP checks were not run; no full verification PASS or production landing claim is made. Existing native build warning states automatic dynload aspect-pack production remains unavailable; the probe does not qualify that path.
