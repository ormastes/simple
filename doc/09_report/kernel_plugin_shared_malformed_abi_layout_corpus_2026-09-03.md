# KPF shared malformed ABI/layout corpus — 2026-09-03

## Scope

The canonical vector source is `src/tool/kernel_plugin_schema/abi_vectors.spl`.
The Simple, C, Rust, and C++ generators project the same nine cases without
changing worker-wire or lint-catalog code.

## Cases

- exact valid prefix;
- append-compatible oversized known prefix;
- truncated prefix;
- declared size beyond available bytes;
- nonzero reserved field;
- payload offset before the declared header;
- payload length beyond available bytes using subtraction-safe bounds;
- misaligned payload offset;
- non-power-of-two alignment.

The C test vectors are emitted only when
`SIMPLE_KPF_INCLUDE_ABI_TEST_VECTORS` is defined, so production consumers do
not retain corpus data. The validation helper remains allocation-free.

## Evidence

- `compiler_spec.spl`: 10/10 PASS, including all four generated projections.
- `c_abi_conformance_test.shs`: PASS under C11 and C++17.
- `generated_sdk_conformance_test.shs`: Rust 1/1 PASS and C++ PASS.
- `generated_abi_layout_corpus_spec.spl`: Simple 1/1 PASS.
- `generated_abi_layout_mutation_test.shs`: mutation rejected.
- `git diff --check`: PASS.

## Result

The remaining REQ-KPF-008 shared malformed native-layout corpus gap is closed
for the first compatibility set. Persistent ABI identities and dense operation
slots are unchanged.
