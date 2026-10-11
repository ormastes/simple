# Bootstrap argument contract CI failures

Status: FIXED (focused script contract); native bootstrap remains separately qualified.

Observed: Linux LLVM job 114511038676 on e03e140 failed the bootstrap argument contract. Required `--jobs-memory-policy` lacked space-form normalization, two help placeholders did not match the documented required-value shape, and the checker treated an early managed-resume dispatch as a missing main-parser option. Its generic invalidation value was also outside the valid build-phase domain.

Repair: normalize the required memory-policy value, advertise `<phase>`/`<dir>`, derive early-dispatch arity from normalization independently of main-parser state, and probe valid invalidation scopes. Keep managed-resume execution and invalid-scope rejection unchanged.

Prevention: the checker rejects invalid scopes and self-tests an accepting-invalid-scope mutant, alongside unknown-argument, optional-consumption, missing-normalization, and help-drift mutants. The conforming fixture also includes a required early-dispatch option.

Validation: focused contract passed 120 checks; both shell files passed syntax checking and the patch passed whitespace validation. No compiler bootstrap was run by these checks.
