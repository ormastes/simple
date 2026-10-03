# Windows native-all sysinfo import libraries

Actual Cranelift Phase2 compiled 1178 objects, then failed at link. In addition to a separate broad host-module import bug, simple_native_all.lib(sysinfo objects) referenced Pdh*, Net*, GetModuleFileNameExW, and CallNtPowerInformation without their Windows import libraries.

The native project MSVC and MinGW configurations now include pdh, netapi32, psapi, and powrprof. These are genuine platform implementations, not runtime stubs. Preserve previously emitted objects and cache when retrying the link.

Validation: focused simple-common regression passed (1 passed, 0 failed), covering both Windows configurations. A clang-cl native executable imports one actual function from each library and runs successfully. Full Phase2 producer link remains dependent on repairing the unrelated broad SFFI host closure; no full compiler qualification is claimed.
