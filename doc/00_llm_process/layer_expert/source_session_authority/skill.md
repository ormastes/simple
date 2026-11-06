# Authenticated source-session layering

Common binding/host values and nogc source host transitions are protocol-independent. Canonical Caret auth owns credentials, principal/workspace mapping and live-manager registration; HTTP owns headers/status and mutex transaction dispatch. app.source_view.service owns source inspection; the MCP adapter does not define HTTP business semantics.

Configure authority only before listener startup. Never derive logical agents from connections, last-read globals, supplied session IDs or SessionExecutionBinding metadata. Restart/expiry/revocation are explicit. Preserve raw source, bounded response and first-help transaction semantics. Full runtime admission remains open pending real manager/listener/thread execution.
