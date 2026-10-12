# HIR archive inventory projection scratch

Status: source reviewed; native qualification pending.

Inventory capture now builds and hashes its metadata in a transient scope, promotes the body-free projection, and closes that scope before validating complete bodies through their existing individual leases. Context verification likewise bounds metadata comparison scratch separately from body validation.

The inventory domain and canonical bytes are unchanged. Conflicting alias metadata is recorded during projection but reported only after the original ordered body checks succeed, preserving body-failure precedence. Existing closed-scope inventory, alias, active/paused ownership and verification controls remain required. No measured RSS improvement or Phase 3 admission is claimed for this source change.
