# Windows standalone core argv selected a legacy array owner

Canonical bug database reconciliation is pending: a qualified self-hosted bug
database runner is not available in this bootstrap lane.

The D6C3 Phase2 producer linked the LSP server from source f46941a142c. Its
initialize request returned JSON and exit 0, but stderr rejected an unregistered
array handle. This is a failed runtime smoke, not an admitted tool.

Static evidence establishes the selected owner: the linked PDB places
`rt_cli_get_args` at section 1 offset 99776 (VA 0x1400195c0). Disassembly
allocates a 24-byte legacy SplArray and initializes data/length/capacity at
offsets 0/8/16. The unused native weak default has section offset 318656.
`runtime.c` deliberately made its argv helpers strong on Windows to avoid
conflicting COFF weak defaults. That selects its legacy array/value ABI even
when `SIMPLE_CORE_C_STANDALONE` requires registered tagged core values.

The repair confines ownership changes to Windows standalone builds: omit the
three legacy argv helpers in runtime.c and make the three core-native helpers
strong. Hosted Windows retains its original strong/weak ownership; Unix is
unchanged. Array registry validation remains intact.

Regression source: `test/04_smoke/core_windows_argv_owner_native.c`. It checks
all three array argv entrypoints, scalar count/index helpers, boundaries, spaces
and UTF-8. Evidence is retained under
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016/core-argv-owner-regression`.
The focused native/core archive link passed 22 checks with exit 0 and empty
stderr. Symbol checks show no legacy argv definitions in the standalone
runtime.obj and all three strong definitions in runtime_native.obj. Compiling
without standalone preserves hosted runtime strong/native weak definitions.

An explicit mixed-TU link without `/FORCE:MULTIPLE` exposed unrelated existing
duplicate runtime symbols; this is not a passing mixed-TU execution claim.
The original tool link already used that policy. Full tool relink/runtime
qualification remains a separate requirement; no production deployment is
claimed here.
