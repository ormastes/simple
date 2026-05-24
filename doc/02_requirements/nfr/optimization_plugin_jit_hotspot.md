<!-- codex-research -->
# Optimization Plugin JIT Hotspot NFR

NFR-OPJH-001: The contract change shall not require dynamic plugin loading in compiler or JIT hot paths.

NFR-OPJH-002: Disabling a JIT hotspot provider shall preserve interpreter/native fallback behavior.

NFR-OPJH-003: Runtime hotspot planning shall require explicit guard facts such as `safe_deopt`; no provider may specialize from hot-count data alone.

NFR-OPJH-004: Documentation shall distinguish compiler optimization rewrites from JIT hotspot plans.

NFR-OPJH-005: Hotspot fact extraction and planning shall be deterministic pure Simple logic so it can run in unit tests without native JIT handles.

NFR-OPJH-006: Performance evidence for hotspot planning shall record command, mode, checksum-bearing rows, and scope limits so interpreter planning costs are not confused with native JIT speedups.
