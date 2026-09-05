# SimpleOS Core Archive Tool Discovery

Source: `test/01_unit/os/simpleos_core_archive_tool_discovery_test.shs`

Evidence class: `host-fixture`.

Using an instrumented archiver, the test verifies that one resolved LLVM
archiver performs both member extraction and final archive construction, and
that a missing configured override fails closed. The fake Simple compiler
means this is tool-routing evidence, not a production core build.

