# Tier C -- Deferred Userland Ports (2026-04-24)

Packages from the Ubuntu install script that are deferred to follow-up /dev runs.
Each requires multi-KLOC implementation or external subsystem support.

## Deferred Packages

| Package | Rationale |
|---------|-----------|
| tar | Multi-KLOC ustar/pax format parser + streaming read/write |
| xz | LZMA2 decoder — multi-KLOC reference implementations |
| unzip | ZIP local+central directory + DEFLATE codec |
| zip | ZIP + DEFLATE encoder |
| jq | JSON parser + path/filter language with pipes, reductions, regex |
| curl | HTTP/HTTPS client with TLS, redirect, auth — depends on TLS stack maturity |
| wget | HTTP/HTTPS downloader — similar to curl |
| htop | Interactive process monitor — requires /proc-equivalent + TUI |
| lsof | List open files — requires kernel fd introspection |
| strace | System call tracer — requires ptrace-equivalent |
| net-tools | ifconfig/route/netstat — requires network stack introspection |
| make | Build system — dependency graph + shell execution |
| cmake | Meta-build system — CMake language parser + generator |
| ninja-build | Build system — .ninja format parser + job scheduler |
| clang | C/C++ compiler — already staged as toolchain wrapper, not native port |
| lld | Linker — already staged as toolchain wrapper |
| pkgconf | pkg-config implementation — .pc file parser |
| python3 | Python interpreter — multi-100-KLOC; violates .spl-only rule if ported |
| python3-pip | Package manager for Python — depends on python3 |
| yq | YAML processor — YAML parser + jq-like filter language |
| p7zip-full | 7z archive support — LZMA/LZMA2/PPMD/BCJ codecs |
| fzf | Fuzzy finder — interactive TUI + ranking algorithm |
| shellcheck | Shell script linter — Haskell-origin, full sh/bash grammar |
| universal-ctags | Source code indexer — multi-language parser |
| psmisc | killall/pstree/fuser — process utilities (ps already in coreutils) |
| procps | ps/top/free/vmstat — process status (ps already in coreutils) |

## Already Covered (Tier A/B)

| Package | Coverage |
|---------|----------|
| bash | SimpleOS shell (shell_app.spl) covers core bash functionality |
| coreutils | 26 tools as shell builtins (head, tail, sort, uniq, cut, tr, tee, wc, etc.) |
| findutils | find as shell builtin |
| grep | grep as shell builtin |
| sed | sed as shell builtin |
| gawk | awk as shell builtin (322-line implementation) |
| diffutils | diff as shell builtin |
| patch | patch as shell builtin |
| tree | Standalone tool (src/os/tools/shell/tree/tree_tool.spl) |
| less | Standalone tool (src/os/tools/shell/less/less_tool.spl) |
| ripgrep | Tier B alias: rg -> grep |
| fd-find | Tier B alias: fd -> find, fdfind -> find |
| bat | Tier B alias: bat -> cat, batcat -> cat |
| silversearcher-ag | Tier B alias: ag -> grep |
| eza | Tier B alias: eza -> ls |
| git | Already an app (src/app/) |
