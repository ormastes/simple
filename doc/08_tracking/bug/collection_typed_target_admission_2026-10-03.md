# Typed collection explanation can inherit host facts for an unknown target

Status: source repair implemented; executable verification NOT RUN.

`mir_target_context_os_from` in `src/compiler/00.common/mir_target_context.spl`
falls back to host OS for unrecognized explicit target text. Its ABI derivation
then defaults from that OS. For example, `x86_64-unrecognized` on Linux obtains
x86_64/linux/gnu facts. The typed explanation helper currently requires only a
nonempty target string, and the direct compiler explanation API does not add
strict target admission. The narrow literal consumer can therefore describe a
consumed plan using host facts that were not established for the requested target.

Do not treat CLI native-build target validation as protection for the direct
explanation API. Do not change shared target fallback semantics without auditing
existing callers. Add an explicit collection target-admission result at the
driver boundary: recognized host requests may use host facts; unsupported or
malformed explicit targets must yield an error or an Original decision with an
unknown-target rejection. Carry that result into MIR rather than inferring
validity from normalized arch/OS/ABI strings.

Regression evidence needed: the same parsed literal source at O2 and sufficient
budget must not report `typed_mir=consumed` for `x86_64-unrecognized`; a recognized
Linux triple must remain eligible; actual host requests must be checked against
known host facts. Cover both the public explanation API and optimize CLI.

The repair adds a default-false admission bit derived from exact recognized
target forms before legacy normalization. Host requests preserve the backend
context, including admission and ABI, rather than deriving it again from OS.
The literal consumer checks both admission and supported OS/ABI/backend facts.
Receipts include `target.admitted` for Original and selected decisions. Tests
cover malformed explicit requests, unknown host/backend, explicit replacement
of malformed ambient targets, musl preservation, parsed MIR, and optimize CLI.
These assertions are authored but unrun; production readiness remains unproven.
