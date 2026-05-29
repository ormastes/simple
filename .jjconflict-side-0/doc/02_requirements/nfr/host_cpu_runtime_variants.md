# Host CPU Runtime Variants NFR

- `NFR-001`: Host config reads shall be cached per resolved config path inside the process.
- `NFR-002`: Config writes shall be canonical and deterministic.
- `NFR-003`: Legacy manifests without the runtime-variant index shall continue to parse.
- `NFR-004`: Dynamic loader fallback order shall be deterministic and test-covered.

