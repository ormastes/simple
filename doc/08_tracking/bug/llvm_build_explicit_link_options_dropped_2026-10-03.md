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

Source review found that the old default `libraries: ["c"]` would become
`c.lib` under the MSVC configured-library renderer once forwarding was restored.
The default constructor now supplies no explicit libraries. Target linkers
already own CRT defaults: native_linking.spl uses native_link_std_lib_args for
Unix, and msvc.spl supplies msvcrt.lib in its default Windows library set.
Explicit caller `c` is retained verbatim; the separate Unix-specific
for_simple_cli constructor is unchanged. Regression coverage distinguishes these
cases, including Windows driver options. This is source evidence, not executed
cross-platform link validation.
