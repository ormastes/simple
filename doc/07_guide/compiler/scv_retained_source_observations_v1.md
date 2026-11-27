# SCV retained compiler source observations V1

The first compiler producer slice observes real selected frontend execution
inside the ordinary retained parse loop. It is a diagnostic compiler API, not
an admitted semantic validator or a BuildRunner integration.

Set `CompilerDriver.ctx.config["scv_source_observations_v1"] = "1"` before the
existing `parse_all_impl` phase to retain a copied diagnostic projection on
`CompilerDriver.source_traversal_diagnostic_v1`. Observation failure makes this
explicit requested phase fail; it cannot silently fall back to an unobserved
success. With the config absent, the existing loop uses no observation owner
and performs no added inventory hashing or copying.

The lower-level `parse_all_with_source_observations_v1` API returns the opaque
retained receipt. It invokes that same loop and consumes each real selected
parser result once. Its `projection_v1(driver)` method revalidates the exact
frozen source content/order, compiler identity, traversal generation and
selected frontend context. A later observed or default compiler traversal
invalidates earlier receipts. `close_v1` revokes the retained receipt; copied projections remain
diagnostic historical data.

The subject binds exact presentation paths and module names, source-content
digests in the `simple.source.v1` domain, driver identity and observation
generation. Its context digest covers the actual target, relevant frontend
mode/policy, environment-variant owner/session/generation/cache identity and
compiler context config. It is not a `CompileSnapshotV1` identity and must
never be translated into one by relabeling or hashing an SCV snapshot ID.

The public `parse_all_retained_observation_v1` driver seam owns the retained
loop, avoiding a private method call across compiler owner modules.
Private recording executes the actual selected frontend before adding a read.
Source attempts are marked before parser execution and cannot be retried under
the same receipt. A syntax/provider failure cannot seal the receipt. Observed
function names come from the same `ParserModule.function_order` consumed by
the existing compiler loop; they are a narrow output sample, not a complete
declaration or semantic fingerprint.

The profile bounds the source count by the existing three-payload item limit
and total source bytes by 64 MiB. It rejects duplicate paths/module names,
worker/shard/skeleton, streaming, target-inventory and entry-selected routes.
Those routes need separately implemented observation profiles. Each observed
parse checks the small selected-context/config subject and its exact source
row. Inventory copying/hashing happens once when observation begins; final
projection rechecks the retained inventory using exact text equality. There
are no additional filesystem reads or second parser passes. Performance and
native ownership behavior remain unqualified until actual runtime execution.

Every source-input read uses `SemanticQueryReadManifestV1` with `Unknown`
coverage. The compiler still lacks complete resolver/candidate/directory,
generated-input/provider, trait/coherence, aspect/order, macro/CTFE and verified
body dependency evidence. Ambient environment, external namespace and Unicode
path normalization authority are also unresolved. The five semantic issuer
installation gates and `execute_three_payload_compile_v3` remain closed.
