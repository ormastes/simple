# mcp diag
*Source:* `test/feature/app/mcp_diag_spec.spl`

## Behavior

### When diag_core - severity_tag

- returns [E] for error
- returns [W] for warning
- returns [I] for info
- returns [H] for hint
- returns [?] for unknown

### When diag_core - pad_line

- pads short line to target column
- does not truncate long lines

### When diag_core - parse_diag_output

- returns empty for exit code 0
- parses error bracket format
- parses error semantic format
- parses warning format
- parses multiple diagnostics

### When diag_core - overlay_virtual_text

- shows clean lines without annotation
- annotates line with error entry
- shows easyfix hint when show_hints is true
- hides easyfix when show_hints is false

### When diag_core - compute_delta

- detects resolved diagnostics
- detects introduced diagnostics
- detects remaining diagnostics
- handles mixed delta

### When diag_core - format_delta_text

- formats delta summary

### When diag_core - JSON serialization

- serializes DiagEntry to JSON
- serializes DiagEntry without easyfix
- serializes DiagResult to JSON

### When tool schemas - read tools

- generates simple_read schema
- generates simple_check schema
- generates simple_symbols schema
- generates simple_status schema

### When tool schemas - edit tools

- generates simple_edit schema
- generates simple_multi_edit schema
- generates simple_run schema

### When tool schemas - vcs tools

- generates simple_diff schema
- generates simple_log schema
- generates simple_squash schema
- generates simple_new schema


