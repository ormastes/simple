# Bootstrap flat LLVM receiver/signature corruption

- **Status:** Second source correction implemented; full bootstrap verification
  deferred to the parent bootstrap lane.
- **Owner:** Pure-Simple flat MIR-to-LLVM bootstrap emission.
- **Related fix:** `72b91f37d53` (`fix(bootstrap): preserve flat compiler ownership`).

## Failure

The final bounded Stage 3 attempt cleared the prior export-metadata and null
comparator crashes, completed MIR lowering, and entered real LLVM emission. It
then aborted after reporting 10,459 functions and 157 statics:

```text
compile error: unsupported LLVM value conversion from double to ptr
```

No Stage 3 candidate was produced. The canonical log SHA-256 is
`0866bc41dc6ed7d6641bb9a90c082eb680e811a6f67331e034e1152a566b8202`.

## Candidate root and containment

The retained run proves the rejected conversion and its phase, but it did not
retain caller/callee/argument context. It therefore does not prove which value
or signature was corrupted. The strongest existing candidate is the flat native
ownership failure already fixed on the unintegrated `72b91f37d53` branch:
`register_bootstrap_signatures` constructed a receiver-owned `[text]` array for
every flat MIR function, stored those arrays in `Dict<text, [text]>`, then the
driver crossed print/log and method-return boundaries while the staged
`MirToLlvm` receiver remained live.

The scalar MIR signature tables themselves preserve F64 as tag 5 (`double`) and
aggregate/opaque types as tag 9 (`ptr`); adding a `double -> ptr` LLVM cast would
hide the mismatch instead of identifying its producer. This port is containment
until a fresh Stage 3 either converges or reports the new contextual diagnostic.

## Fix

- Build a one-time scalar name/module index and read bootstrap return and
  parameter types from indexed MIR tables after runtime-declaration dictionary
  misses.
- Resolve an authored basename only when exactly one qualified function owns
  it in the caller module; collisions and runtime-owned names fail closed.
- Emit statics and functions in one receiver method and avoid a mutable static
  dedup dictionary.
- Keep bootstrap string declarations in their dedicated module owner.
- Construct the staged translator only after diagnostics and enrich any future
  rejected call conversion with caller, callee, instruction/block, argument,
  source/target type, and value context.

The focused source-shape contract is
`test/01_unit/compiler/bootstrap/bootstrap_flat_llvm_receiver_ownership_spec.spl`.
The next fresh bootstrap session must run one focused check and then one
cache-preserving Stage 2/Stage 3 cycle; this session must not perform a fourth
cycle.

## First integration cycle

The first Stage 2 integration attempt after the selective port reached link and
failed because the two scalar-index `me` blocks had been placed after the
top-level `bootstrap_llvm_static_index` helper, outside the `MirToLlvm` impl.
The linker correctly reported both method symbols undefined. No candidate was
admitted and Stage 3 did not start. The methods were moved before the impl
boundary, and the focused contract now pins that ordering.

## Second integration cycle: retained receiver dictionaries

The corrected Stage 2 completed and admitted SHA-256
`530779a2240d35bfe7ce8834dfdb203b0f30651113a5708f91f853c3a94d654c`.
Its Stage 3 completed parse (602/602), HIR/MIR accumulation, and entered real
LLVM emission with 10,461 functions, then aborted with status 134:

```text
compile error: unsupported LLVM value conversion from double to ptr function=std.common.format.format_fixed value=%l0
```

This exact diagnostic is retained in
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log` at line
1,617,131. Unlike the prior failure, it identifies a correctly typed `double`
function parameter being requested as a pointer inside the later translated
body, not a named call argument. The selective port had replaced the upstream
scalar scans with two receiver-owned dictionaries containing the entire 10,461
function name index. That recreated the same forbidden lifetime shape as the
removed per-function parameter arrays: large mutable collections remained on
the staged `MirToLlvm` receiver across every function translation.

The correction now performs exact-name and caller-module basename resolution
directly against the immutable scalar MIR tables. Exact and local collisions
return unknown, runtime-owned names cannot borrow a local ABI, and no full-tree
name dictionary remains on the receiver. This is a producer/owner correction;
`double -> ptr` remains unsupported and no cast was added. Full Stage 2/Stage 3
verification is intentionally owned by the parent bootstrap run.
