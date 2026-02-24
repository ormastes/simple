# mcp debug log
*Source:* `test/feature/app/mcp_debug_log_spec.spl`

## Behavior

### When tool schemas

- generates enable schema with pattern param
- generates disable schema
- generates clear schema with destructive hint
- generates query schema with filter params
- generates tree schema with format and expand params
- generates status schema as read-only

### When handle_debug_log_enable

- enables logging and returns status

### When handle_debug_log_disable

- disables logging

### When handle_debug_log_clear

- clears all entries

### When handle_debug_log_query

- returns entries as JSON
- filters by entry_type

### When handle_debug_log_tree

- returns text tree by default
- returns JSON tree when format=json

### Integration Regression (stdio)

- dedicated stdio regression verifies `tools/call -> debug_log_tree(format=json)` returns JSON tree without session drop

### When handle_debug_log_status

- returns current status

### When debuglog resource

- handles /status query
- handles /entries query
- handles /tree query
- handles /text query
- returns error for unknown query

