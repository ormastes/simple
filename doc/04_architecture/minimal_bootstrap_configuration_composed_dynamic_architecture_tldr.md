# Minimal-Bootstrap Dynamic Composition — TLDR

Purpose: normal feature edits rebuild the smallest named provider or composition projection while an unchanged `simple-core` loads one immutable `.sci` image.

Core decision: SDN is compiled by low-dependency `simple-configc` into `SimpleCompositionImageV1`; the core loads identity-locked providers through `SimpleProviderQueryV1`, with `SimpleCliCommandV1` and `SimpleAppLaunchV1` as the first public contracts. SCI projects launch policy into the existing `SimpleArtifactManifest`; it is not a second manifest.

Startup maps and validates one indexed image. Help reads command summaries without provider load. Dispatch performs indexed binding and generation lookup, never text parsing, directory scanning, source compilation, or a subprocess.

Invalidation uses typed edges and edge-relevant digests. Unchanged results stop propagation; action metadata and CAS bytes are separate; cache format changes create namespaces. `Unknown` compatibility rebuilds and never authorizes reuse.

Full bootstrap requires a typed incompatibility or explicit convergence/trust/DDC target. App metadata and provider-private changes are never bootstrap reasons.

CLI-0/1/2 are static recovery, essential commands, and extended providers.
B1/B2/B3 are Rust-seed, pure-Simple bootstrap, and admitted self-host producers;
P0/P1/P2/R0 are core, essential, optional, and release products. Acceptance uses
structural work counters; timing/RSS are observational. No bootstrap begins
before its typed reason receipt exists.

Next paths: `doc/05_design/minimal_bootstrap_configuration_composed_dynamic_architecture.md`, `doc/03_plan/sys_test/minimal_bootstrap_configuration_composed_dynamic_architecture.md`, `src/os/kernel/loader/artifact_manifest.spl`, and `src/compiler/35.semantics/interface/compile_interface.spl`.
