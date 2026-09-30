# Rejected package-index generations retain compatibility markers

Owner: seven-plan parent lane, item 6. Status: fixed in source; production verification pending.

`src/app/compiler_entrypoint/index_compatibility.spl` returns false for an
unsupported graph schema or an empty variant digest before clearing environment
markers from an earlier graph. Subsequent consumers can still observe the old
producer, root generation, and variant despite the failed publication.

The pure-Simple owner must clear all three markers on rejection. The regression
in `test/01_unit/app/compiler_entrypoint_index_compatibility_spec.spl` covers
both rejection paths and retains the existing valid-graph/binding-only case.
This is cache-publication failure handling, not complete package-index admission
or host qualification. No source changes outside the pure-Simple owner are needed.

## TDD evidence

Windows Phase 1 diagnostic before the fix: 2 executed, 1 passed, 1 failed;
the old producer digest remained after the rejected publication. After the
fix: 2 executed, 2 passed, 0 failed, exit 0. A separate WSL Phase 1 diagnostic
also executed both cases and passed, exit 0. Logs are retained under
`build/native_probe/index-compatibility-tdd/{red,green,wsl}.log`.

The owner now attempts every environment clear without short-circuiting and
also clears partial publication if any marker write fails. The environment
write-failure branch has source review only; no failure injection is claimed.
This does not make process environment publication transactional between
concurrent requests; callers still require their existing request ownership.

Windows runner SHA-256: `6456107ce86e91d06a03171873b141632b819b8a59637f9fab414e0dcee0dae6`.
WSL runner SHA-256: `0c1733208ab4a94c6508b6192fb1d4955b598f15d492864ab159a24db7875df6`.
Both are the previously identified Phase 1 seeds, not admitted Stage 4 tooling.
The exact command suffix is
`test test/01_unit/app/compiler_entrypoint_index_compatibility_spec.spl --mode=interpreter`.
Diagnostic docgen reported one complete document and zero stubs; admitted
SPipe/docgen, required compiler/lib/MCP/LSP checks, and native evidence remain open.
