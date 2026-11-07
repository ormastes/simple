# Native outline inline body consumes the next declaration

Status: source repair extracted; verification waiting.

The canonical skip_block started at indentation depth one even for an inline expression with no matching dedent, consuming following declarations. The retained repair bounds inline scanning at the structural newline and preserves existing native assembly/opaque-block capture. Indented depth handling is unchanged.

Consecutive inline functions, class methods plus an outer declaration, nested multiline bodies, inline assembly, opaque blocks and Unicode byte spans are asserted through the real released TreeSitter API in `test/01_unit/compiler/frontend/native_outline_declaration_boundaries_spec.spl`. Runtime/docgen and compiler/MCP/LSP qualification are **NOT_RUN**, not PASS.

Provenance: initial production extraction was unchanged from checkpoint `39563cbed06` and PR7265 head `dd3444e346d436ab9bb1a3b5dc8e91e5a9a1b47e`, Git blob `72e5992e41a26e0a0936ec8cb00f48450013866a`. Isolated release base `1e6c8d5df6f66dc7bee9fc7a894e0c086e2a03cd` had owner blob `e925b2406bab5af8f601478b0fd6f2030396db10`. The retained source review reported no unresolved blocking finding for this owner. This extraction does not reset historical build/hardening budgets or qualify the broad unfinished PR7265.

The source-view plan, transport/session behavior and final-source runtime/performance acceptance remain separate outstanding work.

Extraction review found that the canonical lexer emits DotDot and Ellipsis for multiple leading dots. The extracted owner now consumes those actual prefix tokens, with direct parent/triple-parent/group/star controls and a DotDotEq rejection control. This reviewed delta changes the retained postimage; it is not a byte-identical landing of checkpoint39563. Runtime remains NOT_RUN.
