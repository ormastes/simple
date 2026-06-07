# Comparison Against `simple_language.md`

Date: 2026-06-07

Source article: `doc/07_guide/language/simple_language.md`

## Verdict

The article is directionally correct and publishable only with qualifiers. The central LLM-scale thesis is supported by repo evidence: Simple's mock policy, SPipe tests, SDoctest, traceability, generated spec docs, primitive-public-API linting, architecture boundaries, parser-friendly macros, Lean workflow, and bounded backend work all align with the claim that the toolchain acts as reviewer.

The strongest required edits are precision edits, not a rewrite:

- Replace "high-robustness mode" with deny-level match-exhaustiveness lint configuration.
- Say "no user-level `null`; absence is `nil`/`Option`" instead of absolute null claims.
- Qualify runtime families and pointer claims.
- Replace the GUI section with bounded UI/web/rendering/debug facts.

## Claim Comparison

| Article area | Result | Comparison |
| --- | --- | --- |
| 1.0.0-beta status | Supported | `VERSION` and the latest tag are `v1.0.0-beta`. |
| 4,067 tests in 17.4s | Supported as dated snapshot | README says this for 2026-02-14; do not present as freshly run. |
| System-test mock ban | Supported | SPipe mock modes and execution tests exist. |
| Anti-dummy / anti-stub | Supported | Lint and verify gates exist. |
| Duplication gate | Mostly supported | Docs and duplicate-check tool/tests exist; exact `build check --full` wiring was not traced in this pass. |
| Primitive public API lint | Supported | Rust and Simple lint code exists. |
| `unit` / `newunit` | Supported | README/parser evidence exists. |
| No null | Qualified | Better: no user-level `null`; absence uses `nil`/`Option`. |
| Exhaustive match | Qualified | Exhaustiveness lint exists and can be denied; default is not always error. |
| High-robustness mode | Not proven | Replace with strict lint or `@deny(non_exhaustive_match)` wording. |
| Minimal public surface | Qualified | `__init__.spl` and structured export boundaries exist; universal "no `*` export" was not fully proven. |
| Lean workflow | Supported with bounded scope | Deterministic generation/inventory/checking/state reporting is the supported claim. |
| Runtime families | Bounded | Documented, but evidence is strongest for declared matrix subsets. |
| Target presets auto-restrict imports | Not proven | Remove or mark as design intent. |
| Five pointer types including GC | Not proven | Parser evidence supports unique/shared/weak/handle plus borrow/raw forms; GC belongs to runtime families. |
| Handle as checked pool index | Conceptual/bounded | Syntax/runtime hooks exist; full semantics need confirmation. |
| Parser-friendly macros | Supported | Registry/validation/tests exist. |
| SDoctest | Supported | Runner, arg parsing, and discovery tests exist. |
| SPipe-generated docs | Supported | `doc/06_spec` mirror rule and generator exist. |
| Math/loss/nograd | Bounded | Parser/tooling/examples exist; broader autograd runtime remains target-scoped/in progress. |
| VHDL/baremetal | Bounded | Hardware-oriented subset and lanes exist; not arbitrary Simple-to-FPGA. |
| SFFI | Supported subset | Support matrix covers imports/exports/callbacks/layout/tests. |
| AOP | Bounded | Predicate pointcuts/weaving exist within support matrix. |
| GUI status | Understated | Native GUI is unfinished, but web/TUI-web protocol, Draw IR, browser rendering, WASM contracts, and UI-access MCP tools are real bounded surfaces. |
| Pure Simple status | Qualified | Rust remains the bootstrap seed and host substrate; pure-Simple self-hosting is verified by bootstrap stages, not by removing every Rust source file. |

## Recommended Article Shape

Keep the article's first-person thesis. It is stronger than a feature catalog.

Use four levels of confidence:

- Shipped: SPipe, SDoctest, mock policy, anti-stub gate, primitive API lint, `unit`/`newunit`, parser-friendly macros, Tree-sitter/LSP/MCP tooling, SFFI subset, loader plumbing.
- Bounded: Lean, runtime families, LLVM matrix, VHDL/baremetal, AOP, deep learning/autograd, GPU/CUDA, UI/web/WASM rendering.
- Roadmap: native/user-facing GUI polish and a unified TUI/GUI/web component surface.
- Design intent: high-assurance defaults for generated code and strictness that can be dialed by context.

## Open Checks Before Public Release

- Confirm the final release tag and binary asset names for `1.0.0-beta`.
- Decide whether README should update stale `v0.6.1` install snippets before the article links to binaries.
- Trace the exact `simple build check --full` command chain for duplication and coverage.
- Confirm whether `--doctest` remains a real alias or only a README compatibility note.
- Confirm final public wording for handle pointers and target-preset family restriction.
