# Worker advice inventory classified its own strings/comments as advice

Status: classifier repair verified natively; producer rebuild and full
qualification remain pending. Source base: release/1.0.0 at
4d7dda0c117c375568f27feb6936bf76ade808a4.

## Failure and requirements

The frozen full-CLI qualification failed in all four workers with
`FILE-WORKER-E-CLOSURE-INCOMPLETE: aop advice outside import closure`, naming
`driver_worker_surface_closure_v1.spl`. That file contained no actual advice:
its comments and `source.contains("pc{")` string satisfied its own classifier.

- REQ-ADVICE-SCAN-001: retain real `on` advice declarations, using exactly the
  parser's one-or-more spaces/tabs followed immediately by `pc{` lookahead.
- REQ-ADVICE-SCAN-002: comments, ordinary/raw/triple strings and escaped quotes
  must not manufacture global advice roots, including the classifier source.
- REQ-ADVICE-SCAN-003: if a candidate-containing source cannot be lexed, retain
  it conservatively rather than silently omitting possible global advice.

The original qualification log is
`/home/yoon/dev/simple-bootstrap-qualification-20261106/build/bootstrap-qualification/full-cli.log`.
This is distinct from the additional TLDR planner defect: actual advice roots'
imports must enter the plan even when targets do not import the advice module.
That planner repair is a separate lane. The readiness guard stays unchanged.

## Design and ownership

`driver_advice_scan_v1.spl` reuses incremental `CoreLexer` tokens. It does not
create a token vector or implement a competing comment/string lexer. An
initial length-aware marker filter avoids lexical work for non-candidates.
Only an identifier token exactly named `on` receives the parser's raw inline
lookahead. Lexer error/unknown token outcomes retain the candidate. The
wrapper saves/restores core token slots and temporarily suppresses token-env
publication while scanning. The production worker classifier delegates to it.

The streaming scan uses the existing lexer's source-character storage and
current token; it does not retain all tokens. The native 21-case probe used
8,888 KiB maximum observed process-tree RSS. This small fixture is not a
whole-tree performance qualification.

## Native evidence and bounded attempts

Immutable self-hosted producer SHA256:
`43f9a6fc68ac232fcb3d28b0a28ada8fba5b04f5e16326e8f122d09208671c5f`,
with its matching opus-10 `host-gpu` runtime capsule, aarch64 Cranelift.

1. Per-file baseline: requested four workers under 24 GiB. Admission clamped
   to one and refused the pool. Retained `build-cap24-refused.log` and receipt.
2. Per-file baseline under the canonical 48 GiB ceiling: failed HIR completion
   receipt publication (first error), followed by ledger-blocked cascades;
   peak 3,463,732 KiB. Retained `build-perfile-receipt-failed.log` and receipt.
   This is a separate bootstrap failure, not repaired by the scanner change.
3. Explicit whole-program diagnostic, normal enforced guard: baseline built
   and executed. The exact original substring predicate failed 14 of 21
   assertions, exit 14. Initial parse-shard crashes/reclaim were retained;
   the same bounded attempt subsequently completed. No manual restart.
4. Same guarded diagnostic route after the classifier repair: native build
   exit 0; executable exit 0; `assertions=21 failures=0`.

After build peak process-tree RSS: 2,974,228 KiB under a 25,165,824 KiB cap.
All attempts used the canonical process-group timeout/RSS owner. The
whole-program diagnostic explicitly set `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`,
`SIMPLE_UNIT_TLDR_IMPORTS=0`, `SIMPLE_TLDR_IMPORTS=0`; global AOP weaving and
normal guards remained enabled. Private caches and failed receipts were
preserved under the owned worktree's `build/advice-scan/` tree. Compatible
frontend entries were reused; changed HIR/native outputs were isolated.

Baseline native executable SHA256:
`e947bf136b98fcdfd2ecf446d63efb323db8de8a466702a6a7a8b4a5f71d5c9d`.
After native executable SHA256:
`d5e2ecbbf7db9538a2e72457f438571f5397d42b89e9d0c2932d2d10001177ee`.

## Qualification boundary

The native probe executes the actual production scanner helper and confirms
21 positive/negative cases. The extended SSpec scenarios in
`worker_mir_child_closure_spec.spl` are prepared but not executed here: no
admitted full self-hosted CLI/test runner is available. Compiler/lib/MCP/LSP
checks, MCP stdio integration, core runtime and native MCP smoke remain
unqualified. Source changes do not alter the immutable old producer; rebuild
it before claiming the default per-file chain now succeeds. No global verify
PASS or Phase-3 admission is claimed.
