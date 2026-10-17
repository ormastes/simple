# Windows core text/bytes and BDD selected legacy owners

Canonical bug database reconciliation is pending: this bootstrap lane has no
qualified self-hosted bug database runner.

Read-only PDB/disassembly inspection of the retained LSP cycle2 binary
`aedce2f5616be6f2ef3f0577b4be396af8470952e88baf06c958405bc8189141`
proved that the mixed runtime selected runtime.c's implementations:

- `rt_text_to_bytes` at VA 0x14001cbd0 uses strlen and allocates an unregistered
  24-byte byte buffer. The generated caller passes tagged text, and the core
  implementation returns a registered tagged byte array.
- `rt_bytes_to_text` at VA 0x14001cc90 copies raw array storage, losing the
  distinction between byte-packed arrays and tagged integer slots.
- `rt_bdd_expect_eq_rv` at VA 0x1400170e0 is a single return instruction. Its
  sibling legacy describe/it helpers also discard their arguments. These
  owners cannot support trustworthy native BDD evidence.

The repair omits only these seven legacy definitions on Windows standalone
core-C; existing native implementations are real strong owners. Hosted Windows
and Unix retain their previous linkage. Validation must include an intentional
unequal BDD assertion recorded as failure, a positive assertion, and round trips
through both packed and slot arrays with UTF-8 and embedded NUL bytes.

Evidence: `C:/dev/simple-bootstrap-storage/phase3-validation-20261016/core-argv-owner-regression/duplicate-owner-review.md`.
Static selected-owner evidence is distinct from a reproduced runtime call.
This repair does not qualify the whole compiler/tool runtime or repair every
duplicate owner. In particular, Windows `rt_remove` remains separately suspect.

Focused native evidence is retained in the sibling
`core-bytes-bdd-owner-regression` directory. The explicit negative mode exited 1
with one example and one failure, and no stderr. The contract run exited 0,
observed both the intentional failed assertion and a passing assertion, and
preserved UTF-8/embedded NUL through both array layouts. A test-only null-safe
empty comparison correction was recompiled and its contract run passed once.
Standalone runtime.obj defines none of these seven symbols; native defines all
of them strongly. Hosted runtime.c compiled without standalone and retained all
seven definitions. The focused link used the real native object and core
archive without FORCE or fabricated symbols. Mixed-tool execution remains a
separate qualification requirement.
