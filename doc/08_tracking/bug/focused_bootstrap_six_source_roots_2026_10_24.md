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

## Native proof4: focused backend admission

The terminal `build/verify/six-root-native-proof-20261024-04/` run built and
linked its harness, then loaded the actual entry and root6-only helper through
parse, HIR, MIR and AOP. Codegen stopped with `PLUG-E-NOTFOUND: backend=llvm`;
no six-root executable success was established.

The harness and focused dispatcher entered the driver without installing the
selected K1 backend table. `CodegenFactory.create` selects from that initially
empty static table; this failure is before dynamic plugin artifact lookup.
The same gap affects production: exact Stage3/Stage4 branches in
`bootstrap_main.spl` return into focused dispatch before the positional route's
K1 installation. The focused plan now admits the existing logical selected K1
composition after argument validation and before run-environment mutation,
reporting policy and table diagnostics on refusal. The fixture's direct legacy
five-root API branch performs the corresponding admission itself. Normal
six-root proof still enters the production focused path; no adapter, provider
ABI, root or native oracle is replaced. Native verification of this repair is
pending the next frozen proof; proof4 remains a failure.

## Proof5 and cycle6 partial results

Proof5's immutable harness compiled and ran the actual six-root case, printing
`six-root-result=24681357`. Cycle6 reused that exact harness and unchanged
source/runtime inputs. Missing-sixth and seventh-root controls both returned 1
with their specific diagnostics and no artifacts. Their receipts remain local
bootstrap diagnostics, not phase admission.

The direct legacy five-root compile failed. Both files loaded, but ordinary
parsing logged an invalid-array diagnostic and HIR lacked the helper's module
surface. Read-only review found a separate entry-authority difference: focused
dispatch publishes the entry, whereas the direct fixed API only places it in
the input slots and does not publish compiler-owned entry authority. The
existing public API does not document an ambient entry-environment prerequisite.
This does not yet prove the invalid-array warning's cause. Do not add fixture
ambient state to disguise the compatibility failure. No combined pass receipt
was emitted; legacy compatibility remains a merge blocker. The six-cycle
repository limit was reached, and further fix/verify cycles await an explicit
user exception.
