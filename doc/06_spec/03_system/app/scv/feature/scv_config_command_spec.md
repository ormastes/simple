# SCV configuration command handler

Source: `test/03_system/app/scv/feature/scv_config_command_spec.spl`.
Status: authored manual outline; execution, SPipe generation and maintenance scan **not_run**. This is not a generated passing manual.

The actual production command handler loads a private repository's native config and route table. A schema check returns schema-valid inspection output, leaves the exact source bytes intact and explicitly grants no publication authority. A route query selects `database_data` for a `.sdn` data path. An invalid submitted configuration returns failure and retains its bytes.

The unit companion additionally checks argument rejection before file reads and diagnostic escaping: a diagnostic containing a new authority-looking line must remain SDN string data, while the parsed `publication_authorized` field stays false.

Required runtime evidence remains: actual native CLI process dispatch and exit codes; component scenarios on the admitted host; generated-manual and maintenance review; successful caller/core/MCP/LSP checks. These authored assertions do not supply that evidence.
