# Explicit target watcher acceptance

Requirement REQ-GENERIC-CONFIG-TARGET-002, generic formal hardening §6/P4.

Twelve actual watcher wire/config, driver options, manifest and source-change adapter scenarios. Executable owner: `test/01_unit/compiler/watcher/native_target_transport_spec.spl`.

Status: authored manual; compiler/interpreter/native/SSpec/docgen UNRUN. No test fixture or compiler was executed while preparing this packet. Existing modern SSpec runner and spipe-docgen remain required. Tests call real APIs and existing SMF/daemon codecs; no copied success implementation or replacement runner.

Expected behavior: explicit target survives serialization and regeneration; absent target stays unspecified. Target-only drift rejects existing artifact options. A positive header-only mmap fixture checks only the existing options-loading boundary; it does not establish executable mapping or dependency admission. A header without dependency receipts remains rejected by the regeneration validator. Loaded-record fixture uses actual parsed metadata but asserts only refusal before mapping/service creation, not prior executable ownership. Exact-target text alone cannot authorize reuse when mapped target provenance is unavailable.

Full native target feasibility, real watcher/inline compiler regeneration, cold/warm lifetime/concurrency and required core/lib/MCP checks remain separate unrun acceptance gates.

Cycle 2 LT-01: expected identities are derived from the same normalized `smf_compile_options` as compilation. Opt2 with either false or true requested release hashes as release=true; opt0/false/unspecified-target retains its legacy hash. New submission checks use the actual normalized driver hash and require the absent-watcher diagnostic rather than an options mismatch. The dependency-bearing fixture is produced by `generate_smf_with_raw_code_options`, its canonical parsed header receives the actual driver hash, and live source/dependency files are validated by the production owner. Matching opt2 artifacts must be accepted by watcher validation and standalone mapping; wrong targets and an edited dependency must be refused. No fixture code section is executed and no native code-generation success is claimed. All four new scenarios remain UNRUN.
