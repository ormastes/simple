# Pending bug-fix source audit — 2026-11-07

Scope: the 22 still-open PRs from the original 28-PR aggregation, assessed against immutable release `6b9613f2d27594f25da3443c4e3c30ad473cafb3`. This is source comparison, not execution or closure. Later PR heads and release commits need their own review. Six original PRs already landed through #7404.

| PR | Pinned-source disposition | Decisive owner / remaining evidence |
|---|---|---|
| #7256 | Production repair present; qualification open | `cranelift_codegen_adapter.spl` integer negation uses I64 subtraction then signed narrow reduction/extension. Dedicated source repro absent; do not rewind newer float behavior. |
| #7276 | Repair absent | HIR unit completion/recovery ownership helpers absent; draft terminal fixture and ownership spec remain pending. |
| #7292 | Repair absent | Pending metadata/generic owner promotion and registration APIs absent. |
| #7294 | Repair absent, runtime blocked | Advice-root planner additions absent; retained SIGSEGV and zero assertions, exhausted budget. No rerun. |
| #7299 | Production repair present; qualification open | `switch_operators_calls.spl` checks physical F32/F64 before optional/runtime/extern provenance; no fresh runtime proof. |
| #7300 | Repair absent | Six exported t32 session-state globals remain private. |
| #7305 | Repair absent | MSVC native-link support lists lack `winhttp.lib`; Windows linker acceptance pending. |
| #7316 | Repair absent | GPU dimension path still records nonfatal error and returns zero. |
| #7317 | Repair absent | Unresolved function value still records nonfatal error and emits zero. |
| #7319 | Consumer defect reproduced | Full production C objects: 190 assertions / 25 failures per architecture; draft candidate 190 / 0. See companion report. |
| #7321 | Repair absent | Shared module-path builder appends `/__init__.spl` before file-path caller adds `.spl`. |
| #7332 | Composition repair absent | SCV Wasm C bridge absent from Rust build/portable/Simple nativeall source lists. Existing standalone C callback tests do not establish composition. |
| #7337 | Repair absent, runtime blocked | Rust process tuple repair absent; actual Simple fixture retained exit14. Six-attempt cap; no rerun. |
| #7338 | Partially present | Headroom source selection exists; nativeall power helper and Rust millisecond export absent. |
| #7339 | Rust facade absent | C byte-conversion counterpart exists; Rust aliases missing. Draft has three byte/lifetime tests. |
| #7342 | Rust facade absent | Counted binary stdio exports absent. Draft has nine ABI/bounds/partial-I/O/child-pipe tests. |
| #7343 | Rust facade absent | Lexical normalization export/test module absent. Six retained Windows owner passes do not prove rebuilt consumers. |
| #7345 | Rust facade absent | mtime exports/test module absent; source-matched nativeall integration pending. |
| #7346 | Rust facade absent | filename/extension exports/test module absent; nativeall integration pending. |
| #7265 | Partial umbrella | Ownership subset landed through #7237/#7404; source-session/diagnostic-snapshot work remains absent/unfinished. |
| #7241 | Pinned lifecycle addition absent | Lifecycle contract owner/spec absent; PR has newer commits beyond original aggregate pin and is not declared fully assessed. |
| #7344 | Draft-specific changes not present; newer owners need comparison | Expanded census/temporary-assignment APIs from the pinned draft are absent; existing census and call-root refusal implementations are present. No equivalence or qualification claim. |

The main checkout and all 373 registered worktrees had no `bin/release/*/simple` executable in the bounded availability audit. No Rust seed or provisional executable was substituted for required pure-runtime compiler/lib/MCP tests. Windows evidence is not a runnable Linux compiler. Native C/provider existence is not proof of the separate Rust/nativeall composition.

Only the [baremetal diagnostic and adjacent primitive cases](baremetal_tagged_bool_reproduction_20261107.md) were executed in this turn. Other draft tests were inspected/referenced, not newly executed or claimed passing. Production repair presence for #7256/#7299 is narrower than bug-fix qualification. The outstanding system, integration, SPipe and runtime prerequisites remain open.
