# Build Intermediate Lifecycle NFRs

- Cleanup selection is one bounded directory scan per build, never a repository scan.
- Files younger than 24 hours are preserved to avoid interfering with concurrent builds.
- All generated paths remain under the configured output or centralized storage roots.
- Cleanup failure is fail-closed before compilation; post-failure cleanup reports through the existing build result path.
- Default cleanup must not reduce incremental reuse.
