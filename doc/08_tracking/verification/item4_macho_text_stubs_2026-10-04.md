# Mach-O SDK text-stub verification

STATUS: FAIL — full item4/Phase 4 and five-host qualification remain open.

This lane implements both SDK text formats and routes supported leaf contracts
through actual native file selection and the typed Mach-O builder. Parser
success does not establish complete SDK support: transitive dependencies,
reexports, access rules, weak binding, directives, SDK discovery and actual
Darwin execution remain mandatory requirements.

Initial fixture/file-route intent bc11b811906 preceded root adapter changes;
reader intent ca8bf6a6374 preceded parser implementation. The deployed runtime
directories in both the shared and integration worktrees are absent at this
turn's check. No Rust seed substitute was used. Compilation, SSpec execution,
doc generation, coverage, core/lib/MCP/native checks and performance gates are
UNRUN. No executed RED/GREEN cycle or runtime coverage percentage is claimed.

Explicit .tbd inputs retain deterministic file/library ordering and feed real
file bytes into the reader. Binary inputs retain the validating binary parser.
Runtime archives remain archives only. Parsing/lowering failure cannot fall
through to another provider or publish partial output. Hosted defaults and
managed admission remain unchanged. Parser byte/token/depth limits constrain
parsing after the existing resident file read; they do not enforce whole-job
RSS or bound the allocation of that file read.

Source, external fixture, review and structural evidence will be recorded here
as it becomes available; none replaces the UNRUN runtime gates.
