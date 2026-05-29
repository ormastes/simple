# mcp log store
*Source:* `test/feature/app/mcp_log_store_spec.spl`

## Behavior

### When log_entry_to_json

- serializes a single entry to JSON

### When log_entries_to_json

- serializes empty array
- serializes multiple entries

### When log_tree_to_json

- builds hierarchical tree from nested calls
- returns empty array for no entries

### When format_log_tree_text

- renders collapsed tree with >> markers
- renders expanded tree with v> markers
- renders nested indentation

### When log_status_to_json

- serializes status correctly
- serializes disabled status


