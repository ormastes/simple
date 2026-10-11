# Target 6 pinned warm candidate: direct compile evidence

Status: implementation committed on `work/targets-release-20261010` at
`0306471fe22`; executable and performance qualification OPEN.

The admitted pinned V2/V3 entry closure now carries each selected source digest
into the native-build warm candidate. The candidate writer validates path and
digest shape, rejects duplicate paths, and writes the same sorted receipt rows
without reopening and hashing the frozen source files. The later receipt
promotion and hit validators still hash those files; no zero-open or overall
p95/RSS result is claimed.

## Bounded self-hosted compile

- Compiler: admitted pure-Simple Stage 2 at
  `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
  SHA-256 `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`.
- Command: `SIMPLE_LIB=src timeout 150s <stage2> compile src/app/cli/native_build_warm_receipt.spl --format=smf --output build/mini_builds/item56_warm_candidate_module.smf`.
- Result: exit 1 after 117.796 s. Parse, HIR, and monomorphization completed for 142 modules; MIR reached 142/142 then reported 16 errors. The log is retained at `build/mini_builds/item56_warm_candidate_module.log`.
- The errors include unsupported Result unwrap payload, unresolved methods in SCV/environment/database dependencies, enum payload mismatches, unsupported non-array iteration, and one `B5b: match has multiple wildcard arms`. No error names the changed warm candidate source, but the build is not a PASS. Placeholder MIR warnings for unresolved `split`, `substring`, and `release` also prohibit treating a successful exit as sufficient.

The focused unit assertions are authored but have no executable PASS on this
runtime. The next qualification requires an admitted current-source compiler,
the focused unit spec, and a matched native cold/warm cohort measuring p95 time
and peak RSS under the normalized-sum rule. The ordinary CLI V3 graph publisher,
Item 5 demand loading, and release gates remain separate open work.
