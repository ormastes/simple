# Seed diagnostic can report different roots from flattened import execution

Status: OPEN; inspected resolver disagreement with matching runtime symptoms.
The exact inspected Rust source is not an attestation of the frozen seed binary.
Pure-Simple resolver parity and production caller reachability remain unverified.

Parser diagnostic attempt 2 recorded loaded paths beneath the admitted c48
projection and unchanged source hashes. Nevertheless its persisted frontend
cache header was `spl-fecache-v1`, whereas the pinned source defines and writes
`spl-fecache-v2`. The source-B digest key held source-A's parsed frame. This
invalidates attribution based on loaded-path traces alone; it does not establish
a defect in the current c48 parser implementation.

Inspected owners:

- `src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`:
  `find_project_root` checks importer ancestors for `src` or Cargo metadata.
- `src/compiler_rust/compiler/src/pipeline/module_loader.rs`:
  `resolve_parts_with_search_roots` checks the base import path, then advances
  to its parent before checking `src`. A fixture directly in the project root
  can therefore bypass that root's `src` in this second resolver.

A nested test entry is the proposed source-selection repair for the diagnostic.
It is not a production compiler fix. Loaded/read-path checks, observed cache
version and source-generation behavior must all agree before acceptance. The
available read trace does not cover every direct pipeline filesystem read, so
it must not be promoted to complete executable-provider attestation.

Evidence: `build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/formal/parse-reuse-attempt2/`.
Log SHA-256: `affac2e78c9685469b13861d25d4ae391416f1f99e80f6a90ad55d1eb71c91b7`.
Child exit 37; peak RSS 372,192 KiB; owned growth 725 bytes.

Required regressions: root-level and nested entries select the same owner;
nearby competing shared roots cannot override an admitted project; both resolver
paths agree; cache version/source digest match observed parsed content; missing
imports retain diagnostics; aliases and pure-Simple resolution receive parity
checks. Do not solve this by allowlisting unexpected provider files.
