# Windows C compiler authority design

The selection path is Windows host detection, admitted official-distribution prefix selection, executable version validation, then environment export. The default local prefix and a relocated CI workspace prefix share the same source contract. There is no Windows fallback to LLVM18/21 or an ambient compiler. Inherited CXX is removed and target-qualified CC is bound to the same path as CC. Unix selection follows its existing branch.

CMake's Windows toolchain rejects an explicitly selected non-Clang C driver, binds the admitted clang-cl prefix, queries its executable version, and leaves C++ unconfigured. The tiny native verification project declares LANGUAGES C and rejects a loaded C++ compiler; its C source also fails preprocessing if __cplusplus is defined.

The deny rule is windows_c_compiler_selection with diagnostic W-WIN-CC-001. It is registered in sorted order in static_lint_rule_table. Scope, assignment recognition, and admitted-source authority are separate helpers. The scan should remain linear in source length and avoid repeated whole-source work inside the line loop.

The shell regression uses executable fake version responders only to test selection/error behavior. Real native probes separately use the installed LLVM23.1.1 distribution. The C workload and optimization/runtime settings match between clang and clang-cl; measurements are bounded side-effect evidence, not a claimed speedup.

Self-hosted SSpec, generated-doc verification, and compiler/core/MCP gates remain pending until an admitted runner exists. No release or whole-bootstrap completion follows from the focused shell/native probes.
