# SimpleOS Server Authenticated Entry Wiring

Source: `test/01_unit/os/simpleos_server_authenticated_entries_test.shs`

Evidence class: `source-contract`.

The test requires x86_64 and RV64 server entries to use authenticated media
adapters and canonical execute-open/adoption owners on x86_64, ARM64, and RV64, rejects their legacy
unauthenticated facades, and checks the production rebuild plan selects both
entries. Plan output and source wiring do not prove a build or guest launch.
