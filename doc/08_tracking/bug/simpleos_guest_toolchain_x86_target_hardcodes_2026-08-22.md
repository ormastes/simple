# SimpleOS focused guest toolchain selected x86_64 unconditionally

The filesystem-launched focused tool configured
`x86_64-unknown-simpleos`, selected `CodegenTarget.SimpleOS_X86_64`, called the
x86-only linker entry, and required an x86 CS value after filesystem writes.
Consequently AArch64 and RV64 images could contain the same tool but could not
compile or interpret through an honest target-native route.

The fix centralizes selection in `SimpleOsGuestTarget`, maps the three admitted
64-bit guests to existing codegen targets and the shared linker, and replaces
the app-level CPL rule with a target-local user-context shim. Unknown identities and linker target
mismatches are errors. The RV syscall shim now has a canonical source file;
the RV and generic AArch64 sysroot producers no longer generate duplicate
syscall bodies.

The existing native-link orchestrator's ARM/RV routes are kernel-image owners,
not filesystem userland linkers. The focused guest facade therefore links
those two targets explicitly from `/usr/lib/CRT0.O`, `/usr/lib/SIMPRT.A`,
`/usr/lib/SOSLIB.A`, and `/SYSRT/SIMPLEOS.LD`, while leaving kernel routes
unchanged.

Live timing, peak RSS, optimizer, and QEMU execution evidence remain blocked on
the admitted pure-Simple runtime/bootstrap lane. Static complexity is constant:
one bounded three-way selection, fixed descriptor storage, no collection
allocation, and no additional source-sized copy or loop. On runtime admission,
run the focused unit spec and the existing guest wrapper system spec once per
architecture, then record warm compile time and maximum RSS for the same hello
source and filesystem image.
