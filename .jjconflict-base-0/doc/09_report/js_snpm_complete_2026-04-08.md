# JS Engine + snpm — Implementation Report

**Date**: 2026-04-08
**Scope**: Complete JavaScript engine promotion + snpm package manager

## Summary

Promoted the browser's JavaScript engine from `examples/browser/` to `src/lib/common/js/` as a standard library module, added ES2015+ features, created Node.js-compatible runtime modules, built an ECMAScript conformance test suite, and implemented the `snpm` npm-like package manager.

## Deliverables

### JS Engine (src/lib/common/js/) — 32 files, ~10K lines
- **Types**: JsValue, AST nodes (ES2015+ extensions)
- **Engine**: Lexer, parser (destructuring, spread, let/const), interpreter (array HOMs, destructuring, do-while, new, spread), VM, bytecode compiler, JIT, GC
- **Builtins**: Object, Array (map/filter/reduce/forEach/find/some/every), String, Number, JSON, Promise, Date, Error, TypedArray, RegExp
- **Node modules**: fs, path, process, http, child_process, crypto, os
- **Module loader**: CommonJS require() with spl_modules/ resolution

### snpm Package Manager (src/app/snpm/) — 18 files, ~1.1K lines
- 16 commands: init, install, uninstall, update, publish, run, test, pack, link, list, outdated, search, info, login, logout, version
- SDN manifest parser/writer
- Lockfile (snpm-lock.sdn)
- Semver resolver
- Flat spl_modules/ installer with hoisting

### Conformance Tests (test/js/) — 3 files, 103 tests
- ES5: 54 tests (types, coercion, scope, control flow, functions, objects, arrays)
- ES2015: 38 tests (arrows, let/const, templates, destructuring, spread, classes, array HOMs)
- Node API: 11 tests (path module)

### CLI Commands
- `simple js` — JavaScript runtime (file execution, eval, conformance, REPL)
- `simple snpm` — Package manager (16 commands)

### Browser Integration
- 19 browser files migrated from browser.* to std.js.* imports
- 438 browser tests still pass

## Architecture Decisions
1. JS engine lives in `src/lib/common/js/` (pure library, no OS dependencies)
2. Node.js modules are optional wrappers backed by Simple FFI
3. snpm is pure Simple — JS engine only used for postinstall scripts
4. SDN format (not JSON) for package manifests
5. GHCR/OCI registry protocol (via oras CLI)

## Known Limitations
See `doc/08_tracking/bug/js_snpm_limitations.md`

## Test Results
- JS conformance: 103/103 pass
- Browser tests: 438/438 pass
- Lint: pass
