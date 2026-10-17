# Windows native-all consumer loses LLVM dependencies and print ownership

Status: OPEN. Real Hello native linking fails; no repaired compiler or product
is admitted. Bug database registration awaits its canonical checksummed writer.

The exact diagnostic producer and original failed campaign are recorded in
[the campaign report](../../09_report/smux_windows_bootstrap_campaign_2026-10-16.md).
Frozen source is `f612b3f68d6fc315b44df0cff8ec8a6f1db0f5da`; the editing
source integrates release_phase3 `e37c260fe5dfa6d1fdb23ef0793a11999b548d4f`.

The smallest external reproducer is the existing
`test/04_smoke/windows_native_hello.spl`, compiled by `simple-diagnostic.exe`
with `native-build`, target `x86_64-pc-windows-msvc`, backend LLVM and the
producer's frozen runtime-authority directory. Exact commands and terminal
Job receipts live in the frozen checkout's
`build/smux-windows-bootstrap/diagnostic-relink/root-launch-hello*.sh`.

After supported SCV cold initialization, parsing and HIR complete 1/1.
`root-hello-cold-build.stderr.log` records unresolved `LLVMAddGlobal`,
`LLVMBuildIntToPtr` and other LLVM C APIs from Rust compiler members of
`simple_native_all.lib`. Selecting core-C-bootstrap alone cannot avoid this:
the current native-all selector still adds that archive. The canonical repair
must stage the exact producer-selected LLVM import library in the runtime
authority, bind its bytes in the snapshot, validate it in strict preflight and
feed it through both MSVC linker routes. Ambient PATH lookup is insufficient.

A separate reviewed diagnostic supplies the pinned LLVM 23 `LLVM-C.lib`
through the linker's LINK input. `root-hello-llvm-build.stderr.log` no longer
reports the LLVM API errors; it instead records:

```text
lld-link: error: relocation against symbol in discarded section: rt_value_print
lld-link: error: relocation against symbol in discarded section: rt_value_println
```

Both references originate in native-all Rust runtime cgu11. The command also
includes individually compiled C runtime objects and existing `/FORCE:MULTIPLE`.
Its many duplicate-provider warnings are retained. The exact provider/extraction
root cause and semantics-preserving ownership repair require Astra review;
do not relax unresolved-symbol handling, suppress the errors or strip symbols
blindly. Both terminal attempts exit 1 with the owned Job fully quiescent.

Required removal checks are the original Hello compile and actual output
execution, positive/negative target and authority selection regressions, exact
link-input identity/order checks, and original native provider smoke tests.
Source-level tests and manuals are not execution evidence. Dependent Phase 3
and smux remain blocked until the exact producer compiles and executes Hello.

## Reviewed print ownership repair and actual evidence

Astra inspected COFF section sharing and the alias tail-call relocations.
`rt_value_print` shares a section with Rust `rt_print`; the newline pair shares
another section. The canonical destinations `rt_print_value` and
`rt_println_value` already resolve to the selected C owner. Two thin C exports
beside those functions preserve those exact destinations without changing an
algorithm or swapping raw-string and tagged-value ABIs.

The private shim experiment now compiles Hello and executes it with exact
expected output. Both `root-hello-alias-build.job.env` and
`root-hello-alias-run.job.env` record complete, exit 0, quiescent 1. This is
diagnostic continuation only; canonical producer admission remains absent.

The actual patched C owner also passes a mixed-C/native-all link and call test:
`tagged-print-native-all-{link,run}.job.env`, complete, exit 0, quiescent 1.
`test/01_unit/runtime/tagged_print_word_order_alias_regression.c` invokes the
raw-pointer names separately from both tagged aliases and uses the selected
C constructors for nil, integers, booleans and strings. The MAP binds all six
print names to the patched C object, and actual stdout matches its companion
expected file with only Windows CRLF normalization. Rust-created heap string
interchange is outside this repair; equal word sizes do not prove heap-layout
compatibility.

Earlier mixed tests used an incorrect standalone define with native-all.
Their discarded Vulkan aliases were a recipe defect traced by Astra to the
conditional C host-target getter; corrected native-all flags remove it. No
source Vulkan mutation is justified. Those failed attempts remain retained.
