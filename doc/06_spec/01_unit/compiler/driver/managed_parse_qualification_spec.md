# Managed parser qualification receipt admission

AUTHORED_UNRUN. REQ-MANAGED-PARSE-QUALIFICATION-001 covers the sixteen-field qualification record, a build receipt with only its own digest omitted, strict canonical wire decoding and actual file hash checks. Six scenarios use temporary regular files to verify positive mechanical admission, draft/final separation, mutation of each image/artifact class, independent issuer/target expectations, path refusal and malformed wire refusal. Fixture image bytes and marker text are deliberately synthetic test inputs: these tests do not qualify a compiler or prove that a process executed.

The new `SIMPLE-MANAGED-PARSE-QUALIFICATION-2` and `SIMPLE-MANAGED-PARSE-WORKER-BUILD-1` records use the existing bounded wire codec. Both carry worker path/digest, frontend identity, target, producer path/digest, runtime path/digest, closure path/digest, build path/digest, evidence path/digest, and issuer path/digest. Only the build encoder accepts an empty build digest; the final encoder and admission reject it. Admission requires exact external receipt/issuer/worker/frontend/target expectations, canonical receipts, regular no-follow files, matching hashes, a hash-bound canonical build task, and pinned declared inputs. The worker build options bind the entry, target, runtime root and output exactly once.

This is structural admission of evidence supplied by an independently trusted issuer, not cryptographic proof of execution: possession of the issuer executable's hash is not a signature. The caller must obtain expected issuer and receipt digests from its trusted qualification owner. Marker strings alone are never production authority. Existing `parser_qualifier_main.spl` remains responsible for fresh build, actual parent/worker parsing, failure collection, cache reuse and parity, and repeated source/tool/provider checks. This module neither launches that work nor issues a process receipt. Its source-closure artifact is checked byte-for-byte against the issuer's pinned digest; it does not rescan/requalify live source trees.

Worker owner agreement preserves separation: `managed_parse_group` supplies actual parser results/artifacts and does not import or mint this qualification record. No runtime execution, native link, qualified worker or all-feature completion is established by this source-only patch.

V2 warning-authority additions (AUTHORED_UNRUN, REQ-IM-008/012/016): construct
mechanically pinned receipt files with a canonical V2 frontend identity and its
exact policy marker, then submit a real nested run contract to production
admission with independent expected pins. Confirm successful file/identity
binding, then mutate capture policy, each feature switch, expected CPU and worker
digest and require rejection. Keep every file hash valid while removing,
duplicating or changing the policy evidence marker; each altered framing must
reject. A malformed reserved V2 identity cannot use legacy V1 evidence. These
scenarios prove intended mechanical checks only when executed; they do not
assert that fixture bytes represent a qualified executable.
