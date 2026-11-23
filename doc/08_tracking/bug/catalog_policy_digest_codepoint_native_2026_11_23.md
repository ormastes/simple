# Catalog policy digest text codepoint native lowering

Status: source API repair complete; unsupported `text.codepoint()` compiler/language
owner issue remains open. The supported `char_code_at` implementation is a
permanent repair and need not be retired when that owner issue is resolved.

Frozen Pure Simple producer `7f2fdf0c577fb330ac6b6996fbce8039e61a088cbdfa763ad6a9514fea01e4dc`
failed MIR lowering of `environment_variant_catalog_policy_bridge_v1.spl`
lines 61–62: unresolved method `codepoint`, receiver_has_type=false,
kind=-1. Both calls on a typed text parameter and text literals failed.
Source base: `84ea108c7c9`; LLVM, aarch64-apple-darwin, ABI v1,
core-c-bootstrap runtime, C owner.

Use `char_code_at(0)`, the same supported primitive used by the SHA-256
validator, for the private nibble helper. Its only caller first requires exactly
64 lowercase ASCII hex bytes; numeric offsets 48 and 97 therefore preserve
all accepted values and little-endian words. The validator still rejects
uppercase, Unicode, malformed length, nonhex text, and the undeclared zero
digest. No general text normalization or compiler method fallback is introduced.

Regression: `test/fixtures/bootstrap_builder/catalog_policy_digest_codepoint_probe.spl`
executes the public parser and checks every nibble plus all four words and
negative contracts. Run with the exact frozen native producer; a qualified full
CLI runner is unavailable until P4. Diagnostic object evidence lives outside
normal caches at `/tmp/simple-rc-build-20261122/catalog-codepoint-repair-20261123`.
No compiler or cache admission is claimed.

Bug claim tooling limitation: `sh scripts/check/bug-claim.shs reap` on this
host failed with awk newline errors and `die: command not found`; no successful
claim is asserted. This lane was assigned exclusively by the bootstrap owner.
