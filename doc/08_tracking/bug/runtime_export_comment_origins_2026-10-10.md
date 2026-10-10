# Runtime facade comment-origin misclassification — 2026-10-10

Status: source repair with eight focused Phase1 diagnostic cases passed; broader qualification remains open. This is a permanent parser-hint/facade repair, not a tagged temporary semantic workaround. No canonical bug-database update is claimed by this report.

## Retained failure

Both independent terminal external LLVM and Cranelift Phase4 logs contained 54 lines, including summaries. Each contained 48 repeated invalid-origin diagnostics: four origins repeated twelve times, not 54 unique bugs. The facade advertised `SweeperStats`, `SmfCache`, `SmfCacheManager`, and `native_mmap_file` through nonexistent `compiler.loader.runtime.*` siblings. Their actual declarations belong to `compiler.loader.loader.*`.

The external source HEAD was `5dd9df1faf7c70556fe92a837f70ff786b51fd8b`. Its clean runtime facade matched the release baseline used below. The binaries' complete embedded compiler-source bindings were not established. These failures do not establish that all other Phase4 errors share this cause.

## Cause and correction

`module_surface_export_origin_hints` consumes generated owner comments followed by bare exports. It also consumed explicit `export use owner.{A, B, C}` text as a comma-separated bare-name list, inventing an owner for a valid middle name. The repair recognizes the exact `use` token after whitespace, consumes the marker, and leaves the parsed explicit import as authority. Classification allocates only when an owner hint is active; no extra collection or source pass is introduced. The fail-closed origin validator is unchanged.

Three remaining bare runtime exports now name their actual owners explicitly. The sweeper's incorrect generated-sibling marker becomes an ordinary canonical-owner comment. Its existing explicit export and all public spellings are preserved. The facade corrections can avoid this particular textual trap on old compilers; the scanner change itself requires a newly built compiler. No rebuilt/native/full-product result is claimed.

The landed `ebc9569c69096498952472e3d580bbf9a99e808b` already fixed several facade bindings but left these three names and the scanner unchanged. At release `c48d5fb07cc5d75777c63252f2e0659b9bd8e248`, both affected owners remain byte-identical to the tested baseline. Open PRs 2836, 2837, 2838 and 2840 had no overlap in these owners or the new spec at review time. Current Rust source has no equivalent production generated-comment scanner; no Rust mirror change is justified by this evidence.

## Exact diagnostic identity

- Baseline source revision: `af5ef635e07f3fbf4ed9a0a380509399022e7d6e` plus the two candidate owners and new spec.
- Producer: C642 bootstrap seed SHA256 `c642f683b8a09abbe67dc9970d894eb166c6ab9e83f5a763e75df57e92404a4b`. It is not the default qualified pure-Simple release runtime; its embedded source binding remains unknown.
- Windows Job collector: `8ebd72790408be6ff22541e6771ecd8d823f4a32f4f39c5b03c61e6f0bdd99b8`.
- Candidate scanner: `e4ffb2827b8dc94b0bcd5f041f2efa876455bafa28b2f5abb0b4a8883b9d5271`.
- Candidate runtime facade: `d28ccd3254ee4e6f1d6afe3cf07e88071018b68e6808c2614b567bdd6e173ad0`.
- Exact executable spec: `d8c17f28f07f77768c0cd340456ae1fde7e95157901c4f9906aa623a5908325f`.

The private packet is `build/native_probe/p4-runtime-export-origin-20261010/cycle3/`. It contains 404 admitted source/data/alias files (5,532,249 bytes). Static closure alone was not treated as proof: the final runner rejected outside/unpinned resolved or loaded paths and required actual loaded records for production owners. Root's retained audit checked all404 source hashes, 20 additional pins and257 loaded-owner bindings across admission/spec, with zero issues. Unexpected-load checks are postload validation, not a sandbox guarantee.

| Artifact | SHA256 |
| --- | --- |
| `request.json` | `a636bd931e4392820b08d61f3c79c1b448045f7e1763db55122675a40fdffd0f` |
| `result.json` | `5fd3d22dda85199137598e3b66b0496ece14a64494f5dce91326a9d8c5bb26fe` |
| `source-manifest.json` | `73336886e5dd3687e059a33ac324b83422c033689c33df0f2d0e2fec2196379d` |
| `ROOT_RETAINED_EVIDENCE_AUDIT.json` | `6e2ba599c5d3887db2879a58254da25985f5e1b34477ac74a0234fc57c9265e4` |
| `receipt.env` | `39574edf3a10554d2c4f261cfb715e65f6629c2ad113293c3e1c82d93cf30d0b` |

Canonical feature/mode admission and the spec both exited0 with authentic logs, final Job active0, and no observer errors. All eight declared cases executed and passed without skipping/dropping. Admission elapsed0.992s with78,060KiB sampled aggregate peak; the spec elapsed9.492s with448,028KiB sampled aggregate peak. These are bounded diagnostic observations, not native performance or allocator qualification; sampling can miss instantaneous peaks. The child cap was768MiB with a256MiB observer forecast,60s admission/120s spec deadlines.

Cycle1 stopped at an overbroad preparation closure bound. Cycle2 rejected a historical feature-only path hint missing from the current source. Neither launched a compiler/spec. Final cycle3 succeeded; no repeated green execution or fourth attempt is authorized.

## Remaining gates

The manual mirrors the eight real parser/surface scenarios. Alias binding and complete `register_imported_symbol` error propagation are not proved. Alternative `export M.{...}` syntax remains a separate pre-existing limitation. No full Phase4 product, self-hosted rebuild, native test, large-facade allocation benchmark, full compiler/lib check, MCP/LSP check, MCP stdio/native smoke, or `spipe-docgen` result is claimed. Required broader checks remain UNRUN and block production-readiness/release claims. Shared older/dirty working files were not replaced with whole release owners.
