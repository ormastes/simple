# CS host provider facade exports

Status: OPEN; changed-owner native qualification pending.

Actual4cca CS closure reports missing print_raw and positionedfile names. CanonicalSoSix rawoutput alias and asyncIO reexports bind the existing syncIO positioned providers. Hostfixture then exposed an existing syncIO selfreexport for thread_sleep_ms without an imported provider. Canonical concurrent.thread.thread_sleep supplies the alias; concurrent.thread has no imports, so this adds no IOcycle. No appRT access or host implementation changed.

Real native fixture test/fixtures/lib/caret_cs_host_alias/main.spl verifies missingfile readErr/writefailure and successful SoSix terminalwrite. First failure retained at /home/ormastes/simple-phase4-web-a0-parallel-20261010/leaf-fixtures/cs-host-alias/evidence.json. Followup qualification UNEXECUTED.
