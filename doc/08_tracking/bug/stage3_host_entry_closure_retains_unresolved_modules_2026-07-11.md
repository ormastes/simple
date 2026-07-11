# Stage3 Host Entry Closure Retains Unresolved Modules

The pure-Simple stage3 compiler builds the production hosted WM with
`--source src/os/hosted/hosted_entry.spl --entry-closure`, compiles all source
files successfully, then generates 23 unresolved-symbol stubs. The evidence
wrapper deletes this linked candidate and reports
`production-native-build-incomplete`.

The unresolved object owners include Engine2D Metal/SFFI modules, OS userlib
window/log/fs modules, common binary I/O, and failsafe logging. Removing the
production compositor's only `os.userlib.ipc_protocol` dependency and moving
its method numbers to `common.window_protocol.compositor_methods` did not
change the set. A clean measurement compiled 271 modules with zero failures
and retained the same 23 names, including `_file_metadata`, `_glob_find`,
`_spl_dlopen`, `_unsafe_addr_of`, and `_wm_input_event`.

The compiler must limit emitted objects and unresolved-symbol synthesis to the
reachable function/data closure, or provide a strict mode that rejects and
reports the exact reachability path for every retained unresolved symbol. A
linked artifact containing generated return stubs is not valid host WM
evidence.
