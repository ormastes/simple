# Imported-global address repair: compiler construction blocked

Status: WARN / unverified draft. The completed text/array repair is the separate
base commit `4db13344d89425da8bfdf6fc4b037343291fae62`; its evidence must not
be attributed to this new imported-global repair.

## Reproduced failure and proposed repair

Cranelift rejects imported globals because its existing data SFFI combines
declaration and definition and rejects import linkage. Defining zero-initialized
consumer data would duplicate provider ownership and lose shared mutations.

The draft uses only existing native operations: the provider owns data and an
address-accessor function, and consumers import that function. See
`doc/04_architecture/compiler/cranelift_imported_global_address_v1.md` for the
reserved symbol contract, typed pointer result, ordering, cost, and limitations.

Separately, import registration synthesized storage for private scalar literals
such as `READINESS_FULL`, even though the provider intentionally emits no
storage. The draft imports the exact literal value, preserves initialization
dependencies, and explicitly rejects consumer-created storage for address-taking
of an imported inline-only private constant. Public/addressable bindings retain
their real storage route.

## Evidence and bounded stop

Worktree: `/home/yoon/dev/simple-cranelift-text-globals-20261010`.
Logs: `build/native_probe/imported-globals/`.

- `baseline.log`: the previous native Simple compiler rejects the real
  three-module mutable-global fixture during Cranelift object generation.
- `compiler-build.log`: first authorized bootstrap construction attempt,
  `--threads 1`, preserved private cache, timeout after 180 seconds, exit 124.
- `compiler-build-final.log` / `.time`: second and final attempt, source frozen,
  same cache, timeout after 420.11 seconds, exit 124, peak RSS 1,167,148 KiB.
  Seed aggregate-typing warnings appeared, but no new executable was produced.
  Cache writes occurred; useful cache artifacts were retained.

This is a material construction-time limitation. Earlier literal-only repairs
reused most cached units and rebuilt with two workers in 38–43 seconds. The
new root ran with the required one-CPU budget and introduces a binding type;
broader type/layout invalidation may contribute, but it was not established.
No third construction or fix cycle was started. No Rust/C runtime source was
changed, and no test fell back to the seed.

## Pending acceptance

`test/fixtures/compiler/native_imported_global_storage/main.spl` is authored
but not executed with the draft. Its nine checks cover two consumers sharing
provider storage, writes in both directions, exactly one initializer execution,
and the actual private literal. `private_address.spl` must fail explicitly.

Required remaining evidence: build a native compiler containing this draft;
execute that ARM fixture; inspect provider/consumer object symbols for exactly
one data definition; compile the explicit LLVM 18 RISC-V object; verify the
negative address case; rerun only the failed `dynamic_aspect`/`dynamic_probe`
objects; complete the mandatory compiler/library/MCP/LSP and runtime smoke
gates. No native, full verification, merge, or release PASS is claimed here.
