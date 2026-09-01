<!-- codex-requirements -->

# Lazy system path variable NFRs

- **NFR-LSPV-001 Startup:** an unused template performs zero runtime calls and adds no platform/filesystem implementation to the default startup closure.
- **NFR-LSPV-002 Resolution:** first resolution reads only bounded named variables, performs one bounded template scan, and performs no directory scan or subprocess call.
- **NFR-LSPV-003 Warm access:** repeated resolution is O(1) over the memoized result.
- **NFR-LSPV-004 Portability:** Linux, macOS, Windows, BSD and SimpleOS share one public API; host differences remain behind the system-location owner.
- **NFR-LSPV-005 Safety:** environment overrides must be absolute and NUL-free. Filesystem containment and Windows junction handling remain the responsibility of the anchored-open capability, not lexical templates.
