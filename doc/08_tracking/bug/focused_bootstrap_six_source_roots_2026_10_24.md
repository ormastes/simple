# Focused bootstrap rejects its canonical sixth source root

The canonical bootstrap passes six roots (K1, CUDA, compiler, app, lib and plugin
policy), while focused native-build accepted at most five. A capability probe
against the fresh admitted Phase 2 producer (SHA-256 prefix `30a793`, suffix
`335`) with `SIMPLE_BOOTSTRAP_STAGE3=1`, the canonical six roots and no output
argument exited 1 with exactly:

```text
Error: focused native-build accepts at most five --source roots
```

The source-count rejection preceded output validation. Actual prepatch evidence
is in `/Users/ormastes/wt/release-phase2-review/build/verify/six-root-capability/`:
`pre-fix.stdout`, `pre-fix.stderr` and `pre-fix.rss.env`. This establishes the
original admission failure; it does not establish a successful patched build.

The repair adds `aot_native_project_with_backend_fixed_v2`, accepting zero to six
roots and appending the entry as the final input. It rejects negative counts and
counts above six with `CompileResult.RuntimeError` before compiler work. The
existing five-root symbol remains a validated compatibility wrapper. The focused
CLI supplies the sixth root to v2 and rejects a seventh root. The generic
array-taking API retains its fallback for inputs beyond the fixed capacity.

Seven total fixed inputs now travel through `CompileOptions.bootstrap_input_6`,
its default, source loading, final-entry phase gates, native no-op cache identity,
admitted-task reset, shard input writers and full CLI writers. The generic
bootstrap API also populates the new slot and reexports v2. No generated
backfill, Rust registration or C registration is manually patched.

The changed options record layout requires a freshly rebuilt compatible producer
and matching runtime/backfill closure. Mixing an old producer's record layout
with these source consumers is not a valid verification run. The active Phase 2
worktree and its frozen bootstrap remain unchanged.

Behavioral specs cover ordered six-root CLI admission, seventh-root rejection,
seventh-slot default and final entry, cache changes for the sixth root and entry,
invalid direct API counts and the old five-root positive native fixture.
`scripts/check/check-focused-six-source-roots.shs` requires explicit absolute
paths to a fresh compatible producer and matching runtime directory. It builds
a dedicated harness from the patched compiler/app/lib closure; that harness
obtains argv through the canonical owner and directly calls focused dispatch.
Its native oracle executes a helper available only in the sixth root, requires
an unresolved `sixth_only` diagnostic and normal failure when that root is
omitted, rejects seven roots without an output artifact, and executes the old
five-root API result. Nonzero native program exits fail the script.

Native proof, behavioral SPL execution, full compiler/lib checks and MCP/LSP core
checks are **PENDING** until that compatible rebuild is available. Shell syntax,
patch whitespace and direct environment ownership guards passed; these limited
checks do not imply native or bootstrap success.
