# Cross-Language Startup/Compile Harness Audit

**Date:** 2026-09-03  
**Scope:** Simple, C, Rust, Go, and Python startup/compile evidence

## Existing harness audit

The repository already contains useful but differently scoped evidence:

- `scripts/check/check-cross-language-perf.shs` is a broad 2,604-line runtime, concurrency, size, compiler, loader, and scripting benchmark. It has strong self-hosted admission and checksum rules, but compilation is one subsection and samples are not a compact four-stage compiler matrix.
- `scripts/check/check-startup-perf-budget.shs` measures six Simple-only startup/change lanes against budgets.
- `scripts/check/check-compiler-loader-perf.shs` measures admitted Simple loader behavior, failed probes, p50/p95, and RSS.
- `scripts/check/produce-rust-go-benchmark-evidence.shs` compares an execution workload, not compiler stages.

None provided one reusable, interleaved matrix separating compiler process floor, parse/check, object/SMF production, and native executable production across all five requested languages.

## Implemented harness

`scripts/check/profile-cross-language-compile.shs` adds that focused matrix.

- Every round is interleaved by language to reduce thermal/load-order bias.
- Warmups are excluded; raw measured samples retain elapsed microseconds and maximum RSS.
- Tool path, version, and executable SHA-256 are retained separately.
- Exact per-language stage commands are retained in a command manifest.
- Simple requires an executable that is not the Rust seed plus a verified Stage 3 or Stage 4 provenance receipt.
- Missing tools and Python's inapplicable native stages are explicit `unavailable` rows.
- A failed command yields an incomplete sample set and a nonzero harness exit; it cannot become a zero or ratio.
- Object/SMF outputs must be nonempty; native outputs must be executable and successfully run before their timing sample is admitted.
- Scratch is allocated beneath the centralized worktree root and cleaned. Durable evidence is stored beneath the same root.
- The cache policy is explicitly warm: outputs are unique, while compiler and OS caches are not destructively cleared.

The comparable intent is development compilation: C and Rust use optimization level zero, Go uses its default build mode, and Simple uses the Cranelift native path. Exact commands remain in the harness source; future evidence should add a command manifest if these command lines become configurable.

## Interpretation limits

`process_floor` measures the minimum supported compiler/runtime invocation, not identical internal work. `parse_check` reflects each ecosystem's supported front door: Python performs syntax parsing only, while Rust metadata and Go compile perform more semantic work. Therefore stage rows should be compared with these semantic labels intact, not collapsed into an unsupported claim that all compilers do identical work.

No Simple numbers are reported in this committed audit. A live run may only report them when exact self-hosted provenance verifies. This avoids re-labeling the Rust bootstrap seed or a stale binary as Simple compiler performance.

## Verification

Run:

```text
sh test/05_perf/profile_scripts/cross_language_compile_matrix_contract_test.shs
sh scripts/check/profile-cross-language-compile.shs --runs 9 --warmups 2
```

The first command validates the source contract without fabricating measurements. The second produces host-specific evidence and may explicitly mark Simple unavailable.

The 2026-09-03 smoke used three interleaved rounds and zero warmups. All applicable C, Rust, Go, and Python stages produced complete sample sets. Python's two native-production stages were explicitly unavailable. Simple was explicitly unavailable because this isolated worktree had no executable compiler candidate; no Simple latency or RSS value was emitted. The durable host-specific result remains under the centralized worktree evidence root rather than being committed as a portable benchmark claim.
