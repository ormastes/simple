# Static lock-level implementation evidence

Base: `f5c0f468556`, remote `release_phase3`, verified 2026-10-25.
Owner branch: `work/static-lock-level-20261025`.
Implementation reviewed with Astra; no Rust seed fallback used.

## Bounded source evidence

- `git diff --check`: PASS.
- Direct env/runtime facade guards, working and staged: PASS.
- Executable specs under `doc/06_spec`: 0.
- Codec audit: 190 owners checked; the three new serialized lock owners have
  no findings. The audit fails for existing `par_lexical_bindings`, which is
  also the sole failure on the unchanged f5c0 target (187 owners checked).
  The derived lock rank index is rebuilt/validated from the encoded arrays.

## Qualification

STATUS: BLOCKED — runtime verification unavailable.

Neither `bin/simple` nor `bin/release` exists in the shared checkout or owned
worktree. The separate canonical compiler build is running in another lane.
No compiler/lib/MCP/LSP check, compiled SSpec, docgen, sspec-maintain, runtime
smoke, native CLI rejection or performance/RSS test is claimed to have passed.
The manually reviewed spec companion is explicitly UNRUN. Source checks do
not establish the selected requirement's production acceptance.

## Supported boundary and residual

Implementation covers ranked synchronous function effects and explicit
canonical scalar Mutex callback lifetimes. Unsupported manual guard tracking,
general alias/nominal-effect inference, configured wildcard imports, async
suspension and reviewed exception manifests fail closed in the checked
boundary. Qualification and actual execution must precede an acceptance/done
mark, promotion, release or claim of whole-program deadlock freedom.
