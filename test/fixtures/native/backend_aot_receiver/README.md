# Native backend object-path receiver projection

This fixture checks the seven-argument backend session ABI across three
modules. It extracts the real `BackendSession.compile_aot_into_path` body;
adapter bodies, MIR/storage records and diagnostic persistence are modeled.
It does not compile MIR, load a provider, publish objects, or validate filesystem
safety. The models deliberately reject changed receiver and argument sentinels.

Copy `support.spl` and `main.spl` into a private variant directory. Assemble
`session.spl` from `session_prefix.spl`, the exact production method starting
at `    fn compile_aot_into_path(` and ending before `    me close(` in
`src/compiler/70.backend/backend_plugin/session.spl`, then
`export BackendSession`. Preserve method indentation and include a newline
between the prefix and extracted method. The adapter method signatures mirror
the production object-path signatures. The local builtin `compile_aot_module`
method intentionally retains implicit self: its control test passed unchanged.

Use the pinned bootstrap-only authority and LLVM23 environment recorded in
the linked defect report, with independent variant caches:

```sh
perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=180 \
  --receipt="$probe_variant/build.rss.env" -- /usr/bin/time -l \
  env XDG_CACHE_HOME="$probe_variant/xdg-cache" \
  SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_LIB="$PWD/src" \
  "$probe_authority/simple" native-build --backend cranelift \
  --runtime-bundle core-c-bootstrap --runtime-path "$probe_authority" \
  --entry-closure --threads 2 --cache-dir "$probe_variant/cache" \
  --mode one-binary --entry "$probe_variant/main.spl" \
  --output "$probe_variant/main"
perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=20 \
  --receipt="$probe_variant/run.rss.env" -- \
  /usr/bin/time -l "$probe_variant/main"
```

Require all three exact output lines and exit 0:

```text
diagnostic=closed-diagnostic:backend session is closed
diagnostic=missing-diagnostic:backend session has no AOT adapter
backend-aot-receiver-pass
```

The diagnostic model terminates with 99 on any unexpected path or message;
the returned write bool alone is not an assertion. Native checks use `rt_exit`
because the initial bootstrap projection linked `assert(...)` as an unresolved
`_assert` symbol under strict fallback rejection. That failed build is retained.

Red variants remove only `self, ` from the extracted session method or either
adapter object-path signature. Each must fail. Existing red evidence used an
explicit receiver on the additional local builtin method; an independent
control proved removing it still passes. The committed final fixture matches
that control byte-for-byte, so no unnecessary production local-method edit
was retained. See the report for exact artifacts and run identities:
`doc/08_tracking/bug/stage2_backend_aot_receiver_transport_2026-09-23.md`.
