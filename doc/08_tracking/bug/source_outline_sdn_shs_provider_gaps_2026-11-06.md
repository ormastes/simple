# SDN and SHS structural provider prerequisites

Status: OPEN. Owner: source_view; integration/final reviewer: root.

SDN: `src/lib/common/sdn/parser.spl:174` populates spans with `SdnSpan.at`, whose implementation in `value.spl:15` sets start/end to zero. The parser's values and issue list cannot prove exact subtree byte ends or preserve duplicate-key source occurrences. Canonical SDN lexer tokens currently contain kind/text only. Unblock by extending the canonical lossless span owner and testing comments, duplicate/unknown keys, nested mappings/arrays/tables, Unicode and original ordering; then adapt those actual spans. Do not use canonical re-encoding as original source.

SHS: `src/os/apps/shell/shell_script.spl` returns Stmt/IfBranch objects without source spans and represents a Simple/sosh dialect, not arbitrary POSIX/Bash. The normalization adapter `src/compiler/80.driver/parse_dialect_adapters_v1.spl` documents a historical StmtKind co-import collision; this lane has not reproduced it on the current compiler. Its referenced 2026-09-12 bug file is absent here. Unblock by obtaining a current co-import result, fixing canonical namespace ownership if needed, retaining exact syntax ranges, and binding an explicitly detected/configured dialect. Opening source must never execute it.

Until these prerequisites are implemented and admitted, structural requests for these languages report unsupported; explicit raw remains available. LANG-02/03/04 and their full acceptance rows remain open, not excluded or passed.
