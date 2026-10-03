# LLVM build dropped explicit native dependency options

Source-reviewed defect: `build_native_llvm(BuildConfig)` reduced configuration
to five convenience arguments, losing existing libraries, library_paths and
linker_flags. NativeLinkOptions had no fields to transport them; the LLVM
orchestrator constructed empty final library/path lists.

The repair preserves these declarations through BuildConfig -> CompileOptions
-> NativeLinkOptions -> NativeLinkConfig and includes ordered, length-framed
values in options identity. Empty new options preserve legacy hash identity.
The final canonical linker continues strict input/flag checks and rejection of
ambient SIMPLE_LINK_OBJECTS. No manual linker invocation or admission relaxation.

This does not pin provider bytes or authorize arbitrary libraries automatically.
It restores the existing caller-supplied dependency contract. Final linking is
still performed; external bytes are not represented as object cache authority.
DLL load identity and ORC lifetime remain independent prerequisites. Tests are
authored and unexecuted because no admitted runtime is available in this lane.
