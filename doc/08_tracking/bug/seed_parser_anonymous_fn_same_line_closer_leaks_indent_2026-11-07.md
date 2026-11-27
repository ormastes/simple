# Rust anonymous-function closer leaks owned indentation

ID: seed_parser_anonymous_fn_same_line_closer_leaks_indent_2026-11-07
Status: fix-implemented-verification-pending. No whole-compiler or runtime closure.

The Rust native-project discovery parser rejected the original frozen SDK module at185:1 with an unexpected Dedent. Anonymous-function and regular statement-match paths consumed physical Indent frames but stopped at an enclosing closer without releasing their own frames. This is a distinct Rust-owner defect from the closed Pure parser family `parser_anonymous_fn_block_call_arg_2026-08-03`; that historical row and evidence remain unchanged.

The narrow repair landed in [PR7722](https://github.com/ormastes/simple/pull/7722), merge `1f6277fc959b8124c0baeb6d46baee3ac1daad49`, exact reviewed head `e712ff0ede9775f4cb8c6d7a785684d0cf9d2bfa`. Astra reviewed both production blobs and six exact CRLF-to-LF test/fixture projections. The closer stays unconsumed, and equal-column continuation ownership is preserved. Production owners are `src/compiler_rust/parser/src/expressions/primary/lambdas.rs` and `src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`; executable regression target is `src/compiler_rust/parser/tests/anonymous_fn_closer_boundaries.rs` with its five fixtures.

Actual focused evidence, retained without replay:

- Original component baseline:3 failed,2 passed. Changed parser: the three prior failures passed,0 failed/ignored; the two previous greens were retained. Source/dependency postcheck PASS and quiescent. Receipt `build/review/p2-p3-group-campaign/parser-hir/anonymous-fn-nested-match-closer/changed-component/attempt1-test/RESULT.sdn`, SHA256 `10d60773ef1d6617481881cef5cfb8121fb1c9d6492c1afa834b03804c454bed`.
- Exact original full SDK module SHA256 `b26c7c5060ed5a292e81daff1df7443f519bf75163b1aa80826288c244286f13`: parser-only criterion PASS/exit0 using the existing changed parser, with real registry4args/Lambda1param/2Matcharms/following-top-function assertions. No rebuild or previous-green replay. Probe SHA256 `663427c6dcb90f7d4870f77a306fddf29758b2e81b1a9cf311577cd9d40c5a1f`. Retained `full-sdk-module-proposal/evidence/RESULT.sdn` SHA256 `0083d022d75a486548c2008349117c3764e85d8ac90e030ff7b3f518577d5aa6` under the same review packet; source/tools/dependencies postcheck PASS/quiescent.
- Final PR workflow audit: Required42365683677/job128383123564 SUCCESS; Component42365683749 plan SUCCESS and matrix SKIPPED; RTL42365683732 SUCCESS. The skipped matrix is not a compiler/test pass.

WAIT_VERIFY: new constructor generation, original GDB native-role rediscovery/protocol, HIR/runtime and deployment remain UNRUN. Component AST success and this metadata registration do not qualify those scopes. Original failing artifacts, raw qualified fixtures, LF projections and the continuous campaign ledger remain retained in the review packet. Do not replay prior green criteria merely to update tracking.
