<!-- codex-design -->

# Lazy system path variable implementation lanes

| Lane | Scope | Status |
|---|---|---|
| A | Common resolver, template, override matrices | active |
| B | Pure-Simple typed-string flat-AST parity and `_path` lowering | pending after A |
| C | Contextual `Path` typing, diagnostics and auto-fix | pending after B |
| D | Anchored Windows/POSIX open capability | separate host-security lane |
| Sidecars | N/A in this side conversation | N/A |

Merge owner and final reviewer: primary normal/highest-capability Codex session. Phase A must not claim B–D complete.
