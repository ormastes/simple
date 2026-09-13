# P07 namespace bridge reaches an extern the deployed seed cannot resolve

- Status: OPEN (2026-09-12)
- Component: `src/compiler/80.driver/cache/gateway/cooperative_namespace_gc_begin_authority_v1.spl` (packet P07)
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f9ab5704b`
- Found by: L78-INT regression sweep after merging the L7/L8 V4 packets

## Symptom

```
bin/simple test test/01_unit/compiler/cache/cooperative_namespace_gc_begin_authority_v1_spec.spl
```

| tree | verdict |
|---|---|
| base `e71f20d45212` | `outcome=OK executed=6 passed=6 failed=0` |
| after merging P07 `765f78b2e478` | `outcome=ERROR executed=6 passed=5 failed=1` |

The failing example is "keeps a complete copied contribution request fail
closed without host issuance", and it fails with

```
semantic: unknown extern function: rt_cache_host_namespace_available_v3
```

## Cause

`rt_cache_host_namespace_available_v3` is declared at
`src/lib/common/cache_daemon_host_authority_v1.spl:20`, backed in C at
`src/runtime/runtime_cache_host_authority_v1.c:41` and in the Rust runtime;
all three already exist at the base. What changed is that P07's namespace GC
ownership bridge now REACHES that probe on this path, and the deployed seed
binary does not export the symbol, so the call raises instead of returning
the fail-closed `-3`.

This is the `unbacked extern silent nil` family
(`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`), except
that here it raises rather than answering nil.

## Not fixed here, deliberately

Two candidate fixes are both outside an integration lane's authority:
redeploying the seed so the symbol exists (a bootstrap, explicitly out of
scope for this pass), or changing P07 so that the fail-closed path does not
probe the host at all — which is a semantic change to another packet's
frozen behaviour. Recorded RED rather than skipped.
