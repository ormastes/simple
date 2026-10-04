# Default metadata outside the caller's import closure

Build the directory with `main.spl` as its native entry. The entry imports both
implementation modules, but `caller.spl` only imports the type declaration.
Its `self.inspect()` therefore requires the native project's method-default
metadata, not the direct imported-method collector.

The native run checks three values. Also inspect the lowered call or retained
caller object: the omitted call must supply the nil argument explicitly. A
passing native result alone is insufficient because an unset argument register
can accidentally already contain the nil representation. The pipeline unit test
`native_extension_method_defaults_reach_separate_caller` asserts the supplied
argument directly.
