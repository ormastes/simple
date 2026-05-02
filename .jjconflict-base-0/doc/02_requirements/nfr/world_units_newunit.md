<!-- codex-impl -->
# World Units and Newunit NFRs

NFR-WUN-001: Catalog parsing and normalization shall use committed local SDN data; compiler and tooling hot paths shall not fetch standards data at runtime.

NFR-WUN-002: Linear unit conversion shall preserve exact integer/rational relationships until the final requested numeric representation.

NFR-WUN-003: SFFI-facing `newunit` wrappers shall remain ABI-transparent and must be rejected if their backing type is not supported by the C ABI mapping.

NFR-WUN-004: Verification shall include parser tests, SFFI lint tests, primitive public API lint tests, unit catalog consistency checks, and compiler/tooling smoke checks for compiler or lib changes.
