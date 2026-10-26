# Rust seed silently treats object-output flag as a source path

Status: OPEN_SOURCE_ESTABLISHED_PRIVATE_REPAIR_TESTS_UNRUN.
Bug DB reconciliation pending.

Actual CLI owner `src/compiler_rust/driver/src/cli/native_build.rs` recognizes
`--emit-archive` but not `--emit-object`. Its default branch adds the latter to
source directories and continues through executable linking. An earlier bounded
object diagnostic produced PE executable bytes at an `.o` destination and was
correctly rejected by artifact validation. Repeating that build unchanged would
waste compile/link time without creating a relocatable object.

Private repair `build/native_probe/seed-object-mode-rejection-20261011/candidate.patch`
recognizes the unsupported seed mode and returns an explicit named error before
project discovery or output creation. Two actual CLI-owner tests cover rejection
and absence of the named artifact. Applicability passed; source review and
execution remain pending. Shared source was not changed. This does not implement
seed object emission or qualify the captured seed lineage.

The pure-Simple counterpart already handles object output in
`src/compiler/80.driver/driver_aot_native_output.spl`, including copy/relocatable
link failure reporting. It must keep that supported path, not inherit the seed's
unsupported-mode rejection. Use an object-capable producer for object diagnostics;
report unsupported Phase1 attempts explicitly rather than count them as success.

Astra admitted the current signed patch
`cdb8d444ed59bf4b09205d2d57129cb3bc16870e7f6fec8d69d99da7a549173e`
for source application. The fixtures include argv0 and a later help control:
the baseline reaches help/exit zero without compiling, while the candidate must
reject the unsupported object mode first. This removes unrelated build failures
as an explanation for a passing rejection assertion. Tests remain UNRUN.

Root applied the signed patch only to a private preview and discovered its
postimage differs from the preparer's mixed-line-ending draft. A normalized-text
comparison proves only CRLF differences; shared source remains unchanged pending
review of the actual postimage. The original seal/draft are preserved in the
packet with `PRIVATE_POSTIMAGE_CHECK.json`. No compiled behavior is claimed.


Astra admitted the actual LF postimage 54d3d72e...980f. Root applied the exact signed patch to the unchanged clean owner and verified that postimage. Status: LOCAL_SOURCE_FIXED_TESTS_UNRUN. No index, HEAD or remote changed; compiled CLI qualification remains pending.
