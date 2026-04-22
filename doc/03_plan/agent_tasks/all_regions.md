<!-- codex-design -->
# All Regions Agent Tasks

Filed: 2026-04-22

## Completed This Session

- Parallel local/parser/domain research.
- Requirements, NFR, architecture, design, and system-test planning artifacts.
- Feature-request tracking for work too large for the current window.
- Expression-level raw capture for `schema{}`, `style{}`, `ui{}`, `music{}`,
  `bim{}`, `cad{}`, `city{}`, and `rtl{}` in the Rust parser lexer.

## Next Tasks

1. Implement raw top-level `schema{}` and `style{}` declaration capture in parser/AST/outline.
2. Add parser and Tree-sitter tests for raw domain blocks.
3. Implement `schema{}` contract AST and JSON Schema/Protobuf compatibility exports.
4. Implement `style{}` typed theme/layout subset and map it to existing UI/theme code.
5. Split music, BIM/city, CAD, and RTL hardening into separate implementation tracks.
