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
Explicit caller `c` is retained verbatim. Review of build_simple_cli found no
Unix target restriction, so for_simple_cli also delegates its former c/m/pthread
defaults to the target linker. Regression coverage distinguishes these
cases, including Windows driver options. This is source evidence, not executed
cross-platform link validation.

The invocation change is intentional: the former driver_api facade delegates
to an external selected Simple CLI and cannot transport these full typed link
options. The LLVM build now invokes compiler_driver_create/run_compile in the
currently executing compiler artifact, following the existing in-process
driver_api_native_single contract. It does not select or certify a replacement
external compiler artifact. Runtime/artifact admission remains the caller's
responsibility; no backend execution evidence is added by this source change.

The production build_native_llvm_finish adapter preserves the external facade's
output-file existence postcondition: driver Success without the requested file
is an error before any build-complete message. Driver errors remain errors even
when an old file exists. This check does not prove output freshness or validity.
Its fault-injection specs use a tracked source file solely as an existence
fixture, never as evidence of executable output or compiler success. Tests are
authored and unexecuted.
