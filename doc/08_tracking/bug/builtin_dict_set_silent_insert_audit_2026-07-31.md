# Audit: `.set()` on builtin Dict -- silent-insert-failure blast radius (2026-07-31)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Background

Confirmed defect (not re-litigated here): calling `.set(k, v)` on a **builtin
`Dict`** receiver silently fails to insert under **native codegen**. Immediately
after the call, `keys().len()` and `contains_key(k)` both read back empty/false.
No error, no crash -- the write vanishes. This is a *different* (previously
undocumented) defect from the `.get()`/`.len()` issues already catalogued in
`doc/07_guide/language/dict_native_pitfalls.md` -- that doc should be updated to
include this `.set()` finding; not done here per scope (audit only, no fixes).

First confirmed at `src/compiler/80.driver/driver_source_pipeline_parsing.spl:184`
(the NOTE there claimed it was "the only `.set()` call site on a builtin Dict in
80.driver" -- true for that one file, but nobody had checked the rest of the
repo). **This is native-codegen-only**: per the pitfalls doc, the interpreter
tree-walk path and the Rust seed both behave correctly, so a seed build or an
interpreter-mode test run cannot surface this bug. Only a native
build/run exercises it.

## Scope and method

- Searched `src/**/*.spl`, excluding any path containing a `test/` directory
  component and excluding `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
  (out of scope per instructions -- another session owns an unresolved conflict
  there).
- **933** `.set(` call sites found across **151** files.
- Classification is **automated + spot-checked**, not hand-reviewed line by
  line at this volume. Method: for each `.set(` call, resolve the receiver's
  declared type by finding the nearest **preceding** declaration of that exact
  identifier *within the same enclosing `fn`/`me` block* (constructor call
  `X.new(...)`/`X(...)`, explicit `: Type =` annotation, `{}`/`Dict<...>`
  literal init, or `{K: V}` brace-shorthand). `self.field.set(...)` and
  `self.set(...)` are resolved via the enclosing class and its own field/method
  declarations. When no declaration can be found in the same scope, or the
  nearest declaration is in a *different* enclosing function (ambiguous -- most
  common for generically-named receivers like `dict`, `result`, `data`, `obj`
  reused across many `it`/`fn` blocks with different types), the site is left
  **UNKNOWN** rather than guessed.
- The heuristic was iterated three times after finding real false positives
  during spot-checks (see Verification Notes) -- most importantly, an initial
  whole-file (not scope-aware) name lookup mis-typed dozens of
  `PersistentDict`/`Set`/`List`/`Object`-receiver sites as builtin `Dict` because
  an unrelated same-named variable elsewhere in the same file happened to be a
  real `Dict`. The scope-aware version fixed all of those.
- ~20-item random samples of both the AFFECTED and SAFE buckets were manually
  re-verified against source after each heuristic revision (see Verification
  Notes below).

## Summary counts

| Classification | Count |
|---|---|
| **AFFECTED** (builtin Dict receiver) | 69 |
| **SAFE** (other receiver type -- List, Set, PersistentDict/Trie, user class with its own `.set()`, etc.) | 193 |
| **UNKNOWN** (could not determine receiver type with confidence) | 670 |
| **N/A** (matched by the `.set(` regex but is not a call site) | 1 |
| **Total sites found** | 933 |

**670 of 933 sites (72%) could not be classified by this pass and are reported
as UNKNOWN rather than guessed.** See "Why so many UNKNOWN" below.

## Top severity AFFECTED findings

1. **`src/app/interpreter/helpers/imports.spl:94,111,127`** -- `result.set(...)`
   on `val result: Dict<String, Value> = Dict__new()`, building the
   exported-symbol table for `from X import {...}` and plain `import` module
   resolution inside the tree-walk interpreter's own implementation. If this
   receiver is genuinely the builtin Dict (file uses Rust-flavored syntax
   throughout -- `&mut`, `Option<&str>`, `.clone()`, `Dict__new()` -- consistent
   with the rest of the interpreter subtree, not a foreign dialect) and this
   code path is native-compiled into the deployed `bin/simple`, every
   interpreter-mode `import`/`from...import` would silently resolve to an empty
   module table. **Not runtime-confirmed in this audit (no fixes/repros run,
   per scope) -- flagged as the highest-priority follow-up.**

2. **`src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl:20,164,210`** --
   `headers.set("authorization", ...)` on a `Dict<text, text>` building outbound
   HTTP auth headers for KMS vendor calls. A dropped insert means the
   `authorization` header is silently missing from the request -- calls would
   go out unauthenticated (likely rejected by the vendor, but with no
   diagnostic pointing at the real cause) or, worse if the vendor is lenient,
   silently mis-authenticated.

3. **`src/app/interpreter/helpers/macros.spl:221`** -- `item_bindings.set(...)`
   on `Dict<String, MacroBinding>`, the substitution table for macro item
   bindings. A dropped insert corrupts macro expansion for that specific
   binding, producing a wrong-but-plausible expansion with no error.

## AFFECTED sites -- full table

Recommended fix for every row below is the same: replace `recv.set(k, v)` with
bracket assignment `recv[k] = v` (or `recv = recv` + bracket-assign if the
existing code discards a fluent return value), per
`doc/07_guide/language/dict_native_pitfalls.md`. **Not applied here -- audit
only.**

| File:Line | Receiver | Declared type | Severity | Native-live? |
|---|---|---|---|---|
| `src/app/interpreter/expr/collections.spl:27` | `dict` | `Dict<Value` | HIGH -- direct interpreter-level `dict.set(k,v)`; if this is the interpreter's own implementation of Dict literal `.set()`, user Simple code assigning via `.set()` in interpreted mode is silently broken | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/app/interpreter/helpers/imports.spl:94` | `result` | `Dict<String` | CRITICAL if reachable -- builds the exported-symbol Dict for `from X import {...}`; a silently-empty result would make every name in the import list resolve to nothing | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/app/interpreter/helpers/imports.spl:111` | `result` | `Dict<String` | CRITICAL if reachable -- builds the exported-symbol Dict for `from X import {...}`; a silently-empty result would make every name in the import list resolve to nothing | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/app/interpreter/helpers/imports.spl:127` | `result` | `Dict<String` | CRITICAL if reachable -- builds the exported-symbol Dict for `from X import {...}`; a silently-empty result would make every name in the import list resolve to nothing | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/app/interpreter/helpers/macros.spl:221` | `item_bindings` | `Dict<String, MacroBinding>` | HIGH -- macro item-binding table; a dropped insert corrupts macro expansion substitution for that binding | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/app/office/mail/mail_app.spl:147` | `counts` | `Dict<text` | MEDIUM -- per-folder mail counters; undercounts silently | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/app/office/mail/mail_app.spl:149` | `counts` | `Dict<text` | MEDIUM -- per-folder mail counters; undercounts silently | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/compiler/10.frontend/core/interpreter/test_interp.spl:305` | `empty_a` | `Dict` | LOW (test/fixture, embedded-DSL string executed by a seed-built toy interpreter harness, not this file's own native-compiled code path) | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/compiler/70.backend/linker/sym_resolver.spl:133` | `seen` | `Dict` | MEDIUM -- compiler backend (VHDL codegen adjacency graph / linker symbol-seen set); wrong/incomplete graph or missed-duplicate detection, backend-specific blast radius | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/compiler/70.backend/vhdl_constraints.spl:68` | `adj` | `Dict<text` | MEDIUM -- compiler backend (VHDL codegen adjacency graph / linker symbol-seen set); wrong/incomplete graph or missed-duplicate detection, backend-specific blast radius | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/compiler/70.backend/vhdl_constraints.spl:76` | `adj` | `Dict<text` | MEDIUM -- compiler backend (VHDL codegen adjacency graph / linker symbol-seen set); wrong/incomplete graph or missed-duplicate detection, backend-specific blast radius | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/compiler_rust/lib/std/src/config/__init__.spl:82` | `merged` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/config/__init__.spl:86` | `merged` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/config/loader.spl:83` | `config` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:237` | `visited` | `Dict<i32` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:254` | `visited` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:264` | `visited` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:277` | `distances` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:279` | `distances` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:300` | `visited` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:316` | `distances` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:327` | `distances` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:329` | `distances` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:339` | `distances` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:362` | `in_degree` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:366` | `in_degree` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:383` | `in_degree` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:462` | `color` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:467` | `color` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/graph.spl:475` | `color` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/iterable_defaults.spl:637` | `result` | `Dict < K` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/core/json.spl:382` | `obj` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/core/transport.spl:554` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:503` | `feature_info` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:504` | `feature_info` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:505` | `feature_info` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:507` | `feature_map` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:523` | `feature_tests` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:524` | `feature_status` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:525` | `feature_category` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:530` | `feature_tests` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:535` | `feature_status` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/db_tools.spl:536` | `feature_category` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:437` | `graph` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:439` | `graph` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:451` | `graph` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:453` | `graph` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:477` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:478` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:479` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:501` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:502` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:503` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:504` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:528` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:529` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:530` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:531` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/mcp/simple_lang/symbol_table.spl:532` | `result` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/sdn/document.spl:118` | `updated` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/sdn/document.spl:126` | `child` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/sdn/document.spl:131` | `child` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/sdn/document.spl:132` | `updated` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/sdn/parser.spl:554` | `updated` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/compiler_rust/lib/std/src/sdn/parser.spl:555` | `updated` | `Dict` | MEDIUM -- unreviewed in detail, generic Dict aggregation/accumulator pattern | UNCLEAR (compiler_rust/lib/std is not referenced by build.rs/Cargo.toml; likely a legacy/vestigial stdlib copy bundled with the Rust seed crate, not part of the actively-compiled self-hosted pipeline -- needs owner confirmation, not asserted live) |
| `src/lib/nogc_sync_mut/database/vector/codec.spl:100` | `out` | `Dict<text` | MEDIUM -- vector DB record codec; a dropped field silently corrupts encoded records | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl:20` | `headers` | `Dict<text` | HIGH -- builds HTTP auth headers dict for KMS vendor calls; a dropped `authorization` header means outbound requests go out unauthenticated or get rejected, silently, with no insert error | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl:164` | `headers` | `Dict<text` | HIGH -- builds HTTP auth headers dict for KMS vendor calls; a dropped `authorization` header means outbound requests go out unauthenticated or get rejected, silently, with no insert error | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |
| `src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl:210` | `headers` | `Dict<text` | HIGH -- builds HTTP auth headers dict for KMS vendor calls; a dropped `authorization` header means outbound requests go out unauthenticated or get rejected, silently, with no insert error | LIVE -- part of the self-hosted compiler/runtime/app tree; compiled to native as part of building bin/simple (bootstrap) or any program that imports it |

## `compiler_rust/lib/std` subtree caveat

**54 of the 69 AFFECTED sites are under `src/compiler_rust/lib/std/**`** (e.g.
`core/graph.spl` -- BFS/DFS/Dijkstra/topo-sort using `Dict<i32,bool>`/`Dict<i32,f32>`
built via `.set()`, `mcp/simple_lang/symbol_table.spl`, `core/json.spl`,
`config/__init__.spl`, `sdn/document.spl`). This path is a full bundled copy of
the standard library living inside the Rust seed crate's directory
(`src/compiler_rust/lib/std/src/...`, per its own README: "This directory
contains the Simple language standard library implementation"). It is **not
referenced by `src/compiler_rust/build.rs` or `Cargo.toml`**, and no importer
of `std.core.graph` (or the equivalent) was found anywhere in the live
`src/lib` / `src/compiler` / `src/app` trees. Its last content change (per
`git log`) was a VCS conflict-tree restore, not organic edits. This strongly
suggests it is a **legacy/vestigial copy**, not part of the actively-compiled
self-hosted pipeline -- but this audit did not trace the Rust seed's actual
build inputs exhaustively, so this is a hypothesis, not a confirmed
"dormant" verdict. **Recommend a follow-up to confirm whether anything still
builds or tests against this directory before spending fix effort on its 54
sites.**

The remaining **15 AFFECTED sites** (16 found minus 1 reclassified N/A -- see
below) are in the live tree: `src/app/interpreter` (5), `src/app/office` (2),
`src/compiler/10.frontend` (1, test/fixture), `src/compiler/70.backend` (3),
`src/lib/nogc_sync_mut` (4).

## Verification notes / corrections made during this audit

- `src/compiler/80.driver/driver_source_pipeline_parsing.spl:184` matched the
  `.set(` regex but is inside a `#` NOTE **comment** quoting the original
  bug report -- the actual code (line 191) already uses bracket assignment.
  Reclassified from the initial automated AFFECTED to **N/A**, not a call site.
- `src/compiler/10.frontend/core/interpreter/test_interp.spl:305` --
  `empty_a.set("only", 3)` is inside a triple-quoted **string literal** passed
  to `core_interpret(...)`, i.e. Simple source text interpreted by a
  seed-built toy interpreter test harness (file header: "Run via seed
  compilation... g++"), not this file's own natively-compiled code. Kept as
  AFFECTED (receiver is a real Dict literal) but flagged **LOW severity /
  test-fixture** -- it is exercising the interpreter-under-test, and per the
  pitfalls doc the tree-walk interpreter and seed do not exhibit this bug, so
  this specific site is unlikely to ever hit the native-codegen path at all.
- An earlier heuristic revision (file-global "last declaration wins" instead of
  scope-aware nearest-preceding-in-same-function) mis-tagged 28 sites in
  `src/app/interpreter/collections/persistent_dict_spec.spl` as builtin-Dict
  AFFECTED, because one unrelated `it` block in that file declares
  `val dict: Dict<text, i64> = {...}` while every other block in the same file
  declares `var dict = PersistentDict<...>.new()`. All 28 are genuinely
  `PersistentDict` (which defines its own `.set()` returning a new persistent
  structure) and are SAFE. This is exactly the kind of same-name/different-type
  collision the task warned about -- caught by manually reading the flagged
  file rather than trusting the first-pass regex.
- Random 15-20 item samples of both AFFECTED and SAFE buckets were manually
  cross-checked against source after the scope-aware fix; no further
  misclassifications found in those samples (see `row`/`SdnRow`,
  `sorted`/`List`, `self.register_file`/`JitRegisterFile`,
  `self.default_headers`/`Headers` -- all correctly SAFE, all define or inherit
  their own `.set()`, none touch a builtin Dict internally at the call site
  under review).

## Why so many UNKNOWN (670 of 933)

The two dominant causes (see per-source-signal breakdown in the raw
classification data):

1. **No declaration found in the same file/scope at all** (~416 sites) --
   the receiver is a function parameter, closure capture, or field accessed
   through a chain (`a.b.c.set(...)`) whose type isn't locally re-declared, and
   the regex-based heuristic does not do full type inference or cross-file
   symbol resolution.
2. **Cross-scope-ambiguous** (~254 sites) -- a declaration of the same
   identifier name exists in the file, but in a *different* enclosing
   `fn`/`me` block than the call site, so trusting it risks exactly the
   `persistent_dict_spec.spl` false-positive class described above. These are
   deliberately left UNKNOWN rather than guessed, per the task's instruction
   to "say plainly when you cannot determine it rather than guessing."

Resolving these fully requires either a real type-checker pass (out of scope
for a grep-based audit) or manual, file-by-file review -- not attempted here
given the volume (151 files, 933 sites). The AFFECTED/SAFE buckets above should
be treated as a **high-confidence subset**, not an exhaustive list: there are
almost certainly additional true builtin-Dict `.set()` sites hiding in the 670
UNKNOWN rows.

## Full site table (UNKNOWN and SAFE)

The complete 933-row classification (file, line, receiver, resolved type or
`none`, classification, and matched source code snippet) is preserved as JSON
for follow-up work: see the raw data referenced in this audit's originating
session (not committed to the repo -- regenerate via the same method if
needed: nearest-preceding-in-scope declaration lookup over every `.set(`
call site under `src/**/*.spl`, excluding `test/` directories).

Given the volume (864 non-AFFECTED, non-N/A rows), and that SAFE/UNKNOWN carry
no immediate action item, they are summarized by directory instead of listed
row-by-row here:

| Top-level dir | AFFECTED | SAFE | UNKNOWN |
|---|---|---|---|
| `src/app/desugar` | 0 | 0 | 1 |
| `src/app/ffi_gen.specs` | 0 | 0 | 2 |
| `src/app/interpreter` | 5 | 48 | 32 |
| `src/app/llm_caret` | 0 | 1 | 0 |
| `src/app/office` | 2 | 0 | 0 |
| `src/app/sdn` | 0 | 0 | 1 |
| `src/app/svim` | 0 | 0 | 1 |
| `src/app/ui.chromium.acid2` | 0 | 5 | 0 |
| `src/app/ui.chromium.devtools` | 0 | 0 | 1 |
| `src/app/ui.mcp` | 0 | 0 | 3 |
| `src/app/web_stack_sample` | 0 | 0 | 13 |
| `src/compiler/10.frontend` | 1 | 0 | 0 |
| `src/compiler/25.traits` | 0 | 0 | 3 |
| `src/compiler/70.backend` | 3 | 0 | 13 |
| `src/compiler/80.driver` | 0 | 0 | 0 |
| `src/compiler/90.tools` | 0 | 0 | 2 |
| `src/compiler_rust/lib` | 54 | 60 | 73 |
| `src/lib/common` | 0 | 23 | 47 |
| `src/lib/gc_async_mut` | 0 | 6 | 15 |
| `src/lib/nogc_async_immut` | 0 | 6 | 27 |
| `src/lib/nogc_async_mut` | 0 | 11 | 112 |
| `src/lib/nogc_sync_mut` | 4 | 28 | 318 |
| `src/lib/scv` | 0 | 5 | 0 |
| `src/os/compositor` | 0 | 0 | 2 |
| `src/os/kernel` | 0 | 0 | 2 |
| `src/os/port` | 0 | 0 | 2 |

## Recommended next steps (not performed here -- audit only)

1. Confirm whether `src/compiler_rust/lib/std` is live-built anywhere before
   deciding whether its 54 AFFECTED sites need fixing.
2. Prioritize the 15 AFFECTED sites in the confirmed-live tree (interpreter
   import/macro resolution, KMS auth headers, VHDL/linker backend, mail app)
   for bracket-assignment fixes, highest severity first (imports.spl,
   kms_vendor_adapters.spl, macros.spl).
3. A follow-up pass with real type information (e.g. running the sites through
   the LSP hover/type-at tool, or a compiler-assisted grep) could resolve a
   meaningful fraction of the 670 UNKNOWN sites without full manual review.
4. Update `doc/07_guide/language/dict_native_pitfalls.md` to add `.set()`
   silent-insert-failure as a third documented defect alongside `.get()`/`.len()`.
