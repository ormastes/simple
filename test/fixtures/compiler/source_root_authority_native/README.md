# Native source-root authority regression

These are real compiler input modules, not resolver mocks. Both entry forms
call the imported owner and print its result. The existing
`test/fixtures/compiler/ambiguous_composition_overlay` supplies two competing
numbered `plugins/backend_registry` directories. The local `default` and
`exact` directories each supply a valid owner of that same logical module.

Qualification is pending. Use the coordinated pure-Simple producer, retained
runtime capsule, LLVM 18, and fresh private phase-bound caches for each case.
Do not disable source admission or reuse an output path. Record producer SHA,
candidate source HEAD, fixture hashes, argv, environment, exit, elapsed time,
RSS, diagnostic, and artifact presence. No seed or mocked runner is permitted.

From the immutable candidate checkout, let `F` be
`test/fixtures/compiler/source_root_authority_native` and `A` be
`test/fixtures/compiler/ambiguous_composition_overlay`. Invoke:

```text
<producer> native-build --runtime-bundle host-gpu --runtime-path <capsule>
  <ordered --source flags below> --source <F>
  --entry-closure --entry <F>/<entry> --backend llvm --threads 2
  --cache-dir <private-native-cache> --output <fresh-output>
```

Use `SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_SCV_INVENTORY_COLD_INIT=1`,
`SIMPLE_LLVM_BIN=/usr/lib/llvm-18/bin`, and a private `SIMPLE_HIR_CACHE_DIR`.
Apply the qualification queue's CPU, RSS, wall-time, and core-dump limits.

| Case | Ordered source flags | Entry | Required oracle |
|---|---|---|---|
| Ambiguous grouped import | `--source <A> --source <F>/default` | `main.spl` | Nonzero compile exit, `SOURCE_ROOT_AMBIGUOUS`, no output artifact |
| Ambiguous terminal-name import | `--source <A> --source <F>/default` | `named.spl` | Same rejection oracle |
| Valid default control | `--source <F>/default` | `main.spl` | Compile/execute exit 0; exact stdout `SOURCE_ROOT_DEFAULT_SELECTED\n` |
| Earlier exact owner control | `--source <F>/exact --source <A> --source <F>/default` | `main.spl` | Compile/execute exit 0; exact stdout `SOURCE_ROOT_EXACT_SELECTED\n` |

A different compiler error, missing admission, crash, or timeout does not pass
the negative cases. Selecting either numbered owner or the valid default also
fails, even if compilation succeeds. Resolver-level SSpec assertions do not
substitute for these native pipeline checks.
