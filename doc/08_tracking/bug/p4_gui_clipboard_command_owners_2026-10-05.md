# Phase 4 GUI clipboard command owners

Status: source workaround; native validation pending.

The current 916be producer compiling target 8f7462 completed 2592 of 2593 HIR
modules in `early-p4-full-cli-8f7462-owner-fixes1`. The sole failed module was
`src/app/editor/gui_shell.spl`: unresolved `EditCommand` and
`editor_dispatch_session`, each reported twice for its clipboard-copy and
clipboard-paste paths. Collector exit was 1, RSS receipt quiescent was 1,
abnormal NTSTATUS was zero, and no compiler binary was published. Build log
SHA-256: `12b98bab87ee0b3afdb542125193d4031e30da359396c213c45a8c45f72429d4`.

The GUI calls these two names without importing them. Add explicit imports from
their actual owners: `std.editor.common.types.EditCommand` and
`app.editor.commands.editor_dispatch_session`. The dispatcher itself imports the
same common EditCommand. Do not use the distinct type in editor.buffer.buffer.
No command implementation, clipboard operation, module selection or cache
admission changes. No new runtime allocation or execution is introduced.

Validation: exact source/dispatcher owner review and static guards. Native
validation remains UNRUN until the reviewed cached all-module Phase 4 successor
uses the current producer and 40 jobs. The prior frozen 80-job run is preserved.
Its failed build is not a test pass. Existing editor clipboard tests and that
full closure build are the relevant regression checks; no mock passing test is
added for this import-only correction. General import inference is not claimed
fixed, and this workaround can be retired only after corrected-producer proof.
