# Bootstrap host reserve verification plan

Completed once for this repair:

- Compile the native fixture from unchanged source with immutable opus10 Phase 2
  producer and matching runtime capsule; execute it and retain failure exit 1.
- Compile the unchanged fixture after repairing the production helper; execute
  it and retain the eight-check PASS and exit 0.
- Run working/staged env/process facade guards and whitespace validation.

Pending, owned by root's isolated qualification worktree:

- Build a usable full CLI from the frozen source and run
  `test/01_unit/compiler/driver/native_build_pool_memory_admission_spec.spl`.
- Complete any broader runtime gates required by the compiler qualification
  lane. A failure must remain explicit; the native fixture is not a substitute.
- Review the final exact PR head and checks before merging PR #7257.

Do not rerun unchanged green native checks. No executable SSpec belongs under
`doc/06_spec`; its companion is Markdown only.
