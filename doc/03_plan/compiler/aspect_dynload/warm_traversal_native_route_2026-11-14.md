# Warm traversal: bounded native qualification route

Status: preparation only; no warm native compile or run has been attempted.
Feature checkpoint: `cab5dcaf7b099fdef367a186167970165e17d764`.

## Actual caller and proposed smaller dependency boundary

The authored full fixture at
`test/fixtures/aspect_traversal_warm_driver/main.spl` reaches the production
parser, lowering, HIR validation caller and warm prepare/finish owner. It is the
full-import acceptance fixture, not the initial bounded probe. Importing the
whole CompileContext and generated codec repeats the known large compiler
closure; do not launch that route under a small budget and call timeout success.

Source refactoring approved and authored (unrun):
`TraversalSessionStateV1` owns the existing scalar epoch/session/cache/lease
fields. CompileContext owns one instance of this typed state, with no mirrored marker
fields. All three actual lowering boundaries call begin_epoch; a nonadvancing
epoch sets epoch_admitted=false and cannot become fresh. The actual lowering owner resets
it on a genuine new epoch; the validation caller passes it to the actual warm
prepare/finish functions. A native fixture can then construct the real small
owner instead of substituting a partial or mocked CompileContext. This changes
dependency direction and testability, not the restoration or weaving contract.

The initial projected native entry must call the real prepare/finish owner,
actual aspect validator and existing ordered weaver with real HIR records,
ordinary encoder/decoder, hashes, runtime session and transient-scope functions.
It must exercise cold capture, unchanged reuse, empty-claim removal, mutated
output refusal and missing lease refusal. It may supply an explicitly declared
closed test-universe snapshot; it does not qualify managed inventory admission.
No substitute codec, allocator, matcher, weaver, hash, or fake record is allowed.

The authored coordinator entry is
`test/fixtures/aspect_traversal_warm_coordinator/main.spl`. It calls production
prepare/validate/finish with the real small state, asserts the inserted HIR
callee as well as counts, and checks restored baseline before validation,
unchanged reuse without another retained blob, removal, mutated output,
missing lease and nonadvancing epoch refusal. Its test universe uses real HIR
records and observed image identity, but bypasses parsing and managed inventory
admission. It is not yet projected, compiled or run. The separate full driver
entry continues to cover that intended parser/CompileContext call path.

## Static closure evidence

A source-only analysis of the checkpoint's generated HIR codec found 313
functions and 11,318 lines (428,476 bytes). Reachability from the ordinary
module encoder and decoder, including function-value references as well as
calls, retains 214 complete functions and 5,013 lines. No branch or variant is
removed from a retained function. There are 176 strongly connected components;
the largest contains 21 functions / 1,356 lines, the next 14 / 1,313 lines.
These counts estimate source size only; they are not a memory or runtime result.

The tracked projection recipe must record exact input paths, commit and file
hashes, full retained declaration names, any namespace-only renaming, generated
source hash, external runtime symbol set and intentional exclusions. Include
all transitive codec helpers and actual type definitions. Missing dependencies
are errors, never replaced with permissive stubs. Keep a private Git fixture
with a committed source HEAD, isolated cache and explicit core-C runtime.

## Resource and cycle ledger

The earlier descriptor/pool/driver/MIR package already consumed six cycles.
None may be repeated or reset by changing worktrees. The newer F1 boundary
package consumed two attempts: a missing fixture Git HEAD refusal, followed by
a successful 13-assertion exact-source boundary projection. Those assertions do
not qualify HIR body capture or warm execution and must not be rerun as warm
evidence.

The independent canonical owner consumed two full-import attempts: 4 GiB failed
at HIR6/457; 8 GiB completed HIR458/458 and failed at MIR0/458 in generated codec
(peak 8,412,324 KiB), without an executable. Do not retry that closure unchanged.

After source-closure review and an explicit coordinator resource slot, the
first new warm criterion may use one 60-second / 2-GiB native compile with the
admitted pure-Simple P2, one thread, private cache, and `--runtime-bundle core-c`.
Capture exact command, exit, source/binary hashes and runtime assertions. A cap
hit is a failed attempt and new evidence, not permission for an unchanged retry
or automatic resource escalation. No compile is authorized by this plan itself.

## Still required beyond the scoped warm checkpoint

- Kernel-image memo ownership correction and actual session lifetime evidence.
- Full actual caller native execution, alias/atomicity/refusal assertions.
- Fresh-lowering-epoch cache lookup; current new epochs remain cold.
- Cross-session bounded ownership and persistent semantic/instance cache route.
- Physical allocation evidence: codec allocation reservations are modeled
  accounting, not process-RSS bounds. Eight restore attempts/session is a
  conservative staging limit, not the full scalability goal.
- Generated traversal/plugin interface completion and admitted loading where
  selected requirements demand it; a builtin descriptor is not a loaded pack.
- Same-profile build, MCP/LSP smoke, latency/RSS and end-to-end feature evidence.


The admitted P2 recipe is pinned by the existing receipt
`/tmp/trace-text-provider-newp2-20261114/provenance.sdn`: SHA-256
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`, stage2,
`stage2-admitted/simple` under the immutable pinned-33bc5c6d1d80 bootstrap tree.
Before any execution, verify that exact image against the receipt. The command
shape is `native-build --source src --entry src/main.spl --entry-closure
--cache-dir ABS_PRIVATE_CACHE --runtime-bundle core-c --threads 1 -o ABS_OUTPUT`.
This plan is not an admission of an arbitrary same-named compiler.

The source-only inventory tool and retained SDN are tracked beside the full
fixture under `tools/codec_closure_inventory.py` and `codec_closure_inventory.sdn`.
They include function-value references, retain whole declarations, and explicitly
do not claim the non-codec support closure is ready or compiled.
