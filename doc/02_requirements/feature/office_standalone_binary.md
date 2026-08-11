# Standalone Office Binary Requirements

The user selected a separate Office executable with no bootstrap at application
launch.

- REQ-001: A narrow `office` native entry shall launch without interpreting
  `.spl` source or invoking compiler/bootstrap logic.
- REQ-002: `office calc [FILE] --tui` shall open a fixed, nonempty 20×30 Calc
  terminal surface on supported hosted targets.
- REQ-003: `office calc [FILE] --frame-once` shall emit the same deterministic
  Calc surface without requiring terminal input.
- REQ-004: Calc shall load supported sheet files through a GUI-independent I/O
  owner.
- REQ-005: multiplication and `AVG(range)` shall recalculate in the shared
  formula engine; `AVG` shall be an alias of `AVERAGE`.
- REQ-006: SimpleOS shall use the portable Calc core through an OS-owned entry;
  hosted raw-terminal APIs shall not enter that closure.
- REQ-007: SimpleOS interactive mode shall fail closed until console stdin and
  terminal mode/size ABI are available; frame mode may launch earlier.
