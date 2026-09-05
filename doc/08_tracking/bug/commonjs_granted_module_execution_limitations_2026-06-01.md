# CommonJS Granted Module Execution Limitations

Status: open (triaged 2026-06-11)

Date: 2026-06-01

## Summary

The Node/CommonJS compatibility lane now fails closed for ungranted bare package
requires and supports explicitly granted text-export and source-backed modules,
including bounded package resolution from explicitly granted in-memory
`/node_modules` files. Full host filesystem-backed package policy is still
incomplete.

## Evidence

- `require('missing-package').error` returns `module-denied`.
- `require('missing-package').specifier` returns `missing-package`.
- `require('widget').name` can resolve from an explicit
  `grant_node_module_text_export("widget", "name", "panel")` grant without
  host filesystem access.
- Repeated `require('widget')` returns the same cached exports object for
  mutation/identity behavior.
- Explicit `grant_node_module_source("widget", "...")` grants are visible to
  native `require()` and execute in an isolated CommonJS-style binding scope.
- Source-backed `exports.foo = ...` assignments are returned through
  `require('widget')`, and repeated source-backed `require()` calls reuse the
  same cached exports object for mutation/identity behavior.
- Source-backed `module.exports = ...` replacement objects are returned through
  `require('widget')`, and repeated `require()` calls reuse the replacement
  object for mutation/identity behavior.
- Slash-bearing granted source specifiers such as `./widget.js` resolve without
  host filesystem access and expose deterministic `__filename`/`__dirname`
  bindings for the in-memory module.
- Explicitly granted `/node_modules/<pkg>/index.js` files resolve through
  `require('<pkg>')`, expose the resolved file path through `__filename`, and
  reuse the same exports object across repeated requires.
- Explicitly granted `/node_modules/<pkg>/package.json` plus package main files
  resolve through `require('<pkg>')` without ambient host filesystem access.
- Bounded `fs`/`node:fs` directory methods now expose deterministic
  fail-closed `readdirSync`/`mkdirSync` metadata for focused sandbox examples.
- Granted synthetic `readdirSync` results now expose `firstEntry`,
  `entryCount`, `length`, and string-index `"0"` properties after `mkdirSync`.
- Granted synthetic `readdirSync` results are now real `JsValue.Array` values;
  numeric index access, `join`, and `length` exercise array behavior while
  preserving metadata properties.
- Granted synthetic `mkdirSync(path, { recursive: true })` now walks only
  granted ancestors, records parent-child directory entries for nested paths,
  preserves sibling denial, and exposes a `recursive` result flag.
- Runtime file grants now persist sanitized marker state and the fs
  compatibility path proves a granted prefix authorizes a child path while
  rejecting a sibling prefix.
- Parsed native `fs`/`node:fs` method dispatch now shares captured runtime file
  grants for read, write/read, and sibling-denial checks.
- `node_api_conformance_spec.spl` passes `177/177` with this fail-closed
  package-resolution, explicit text-export/source, stream, timers, and bounded
  fs directory behavior.

## Earlier Rejected Attempt

A bounded `grant_node_module(specifier, source)` prototype was attempted for
explicitly granted non-builtin modules. It exposed runtime gaps that are now
partially closed by `grant_node_module_source`:

- slash-bearing specifiers such as `./widget.js` now work for explicit
  in-memory source grants;
- granted bare-package source is now available to native `require()` and covers
  `exports.*` assignments;
- `module.exports = ...` replacement semantics now return the replacement
  object and preserve repeated-require cache identity;
- bounded `/node_modules/<pkg>/index.js` and package-main resolution now works
  on explicitly granted in-memory files;
- full host filesystem-backed package resolution still needs policy
  integration beyond the bounded in-memory grant model.

## Required Follow-Up

- Add full host filesystem-backed package resolution policy beyond the bounded
  in-memory `/node_modules` grant model.
