# Phase2 release-source HIR startup crash

Status: OPEN. Compiler prerequisite failure; root cause unproven. Initial investigation owner: compiler source pipeline loading.

The user-authorized release-target bootstrap compiled 1,222 pure-Simple modules with zero failures from release source `d66172f8fde` plus the two folded-scalar helper call corrections. The resulting Phase2 compiler SHA-256 is `5e54538de5fc1cacd6e9f92a375fff71e1cab242e6f7e89cd634f38df4f891db`. Its fresh HelloWorld native construction and execution both exited zero with exact `hello` stdout. It is construction-only development tooling, without canonical admission.

Compiling `src/app/traceability/main.spl` then failed in source closure / HIR aggregation: worker exit `-139` (SIGSEGV), no claimed rows, final publication blocked. Both four-worker and one-worker configurations failed. The serial attempt preserved inventory validation and disabled cold initialization after the initial inventory had been constructed. These failures precede MIR and do not establish resolution of the nine earlier MIR errors.

Evidence: `build/native_probe/traceability-release-pass1/traceability-build.log`, `build/native_probe/traceability-release-serial-pass1/traceability-build.log`, and their frontend recovery ledgers. Astra identified the last progress boundary in `driver_source_pipeline_loading.spl`: cached entry source scan, tuple extraction and import processing; no instruction-level cause has been proven. Preserve validators and failure receipts. No application binary was produced.
