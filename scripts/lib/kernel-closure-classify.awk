# Shared kernel/plugin closure classifier (AWK library, sourced with `awk -f`
# alongside a driver script's own `-f` file or `-e`/BEGIN block).
#
# Provides two independent classification axes used by the closure checkers:
#
#   1. `pattern_regex(pattern)` + `module_for(path)` — turns a manifest glob
#      row (`K0|src/compiler/10.frontend/**`) into an AWK regex, and turns a
#      `src/compiler/...` file path into its `compiler.<pkg>.<rest>` module
#      name, exactly as check-kernel-closure.shs did inline before this file
#      existed. Used to classify SOURCE files that live under src/compiler
#      against the manifest's `entries:` rows.
#
#   2. `import_root_class(imported)` — classifies an IMPORT TARGET (the
#      right-hand side of a `use ...` statement) by its leading namespace
#      root, for the roots the manifest's per-file rows cannot see because
#      they are not `src/compiler` paths at all: `plugins.*` -> PLUGIN,
#      `app.*` -> APP, `os.*` -> OS, `weaving.*` -> K0 (the weaver is
#      embedded in the kernel, see kernel_pluggable_partition.md §3.1),
#      `lib.*`/anything else recognised -> LIB (never a boundary violation).
#      Returns "" (unresolved) for `compiler.*` — callers must still walk
#      that case against their own classified module index, since only the
#      caller holds that index.
#
# This file defines functions only; it has no BEGIN/END/main rule of its own
# and produces no output by itself.

function pattern_regex(pattern,    r) {
    r = pattern
    gsub(/[.]/, "[.]", r)
    gsub(/[*][*]/, "\034", r)
    gsub(/[*]/, "[^/]*", r)
    gsub(/\034/, ".*", r)
    return "^" r "$"
}

function module_for(path,    p, n, a, first, prefix, rest) {
    p = path
    sub(/^src\/compiler\//, "", p)
    n = split(p, a, "/")
    first = a[1]
    if (n == 1) {
        prefix = "compiler"
        rest = first
    } else {
        prefix = first
        sub(/^[0-9][0-9][.]/, "", prefix)
        prefix = "compiler." prefix
        rest = p
        sub(/^[^\/]*\//, "", rest)
    }
    sub(/[.]spl$/, "", rest)
    gsub(/\//, ".", rest)
    sub(/[.]__init__$/, "", rest)
    if (rest == "__init__") return prefix
    return prefix "." rest
}

# import_root_class: classify an import target string (e.g.
# "plugins.backend_vhdl.driver.driver_aot_vhdl_output.emit", "app.io.mod",
# "os.smf.smf_generation", "weaving.aop_advice_registry", "lib.text.split")
# by its leading root. Returns one of PLUGIN, APP, OS, K0, LIB, or "" when the
# root is "compiler" (the caller resolves that case itself) or unrecognised.
function import_root_class(imported,    root) {
    root = imported
    sub(/[.].*$/, "", root)
    if (root == "plugins") return "PLUGIN"
    if (root == "app") return "APP"
    if (root == "os") return "OS"
    if (root == "weaving") return "K0"
    if (root == "lib") return "LIB"
    if (root == "compiler") return ""
    return "UNKNOWN"
}

# path_root_class: classify a FILE PATH (not an import string) by its
# top-level source directory, for reuse by callers that walk a file tree
# rather than an import list (e.g. the core-lib closure checker, WP-09).
# Returns PLUGIN / APP / OS / LIB for src/{plugins,app,os,lib}/**, or ""
# for anything else (notably src/compiler/**, which the manifest classifies).
function path_root_class(path,    p, root) {
    p = path
    if (p !~ /^src\//) return ""
    p = substr(p, 5)
    root = p
    sub(/\/.*$/, "", root)
    if (root == "plugins") return "PLUGIN"
    if (root == "app") return "APP"
    if (root == "os") return "OS"
    if (root == "lib") return "LIB"
    return ""
}
