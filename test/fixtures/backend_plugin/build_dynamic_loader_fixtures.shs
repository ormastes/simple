#!/bin/sh
set -eu
PATH=/usr/bin:/bin:$PATH
export PATH

root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
tag=${1:?fixture tag is required}
case "$tag" in
    *[!A-Za-z0-9_-]*|'') echo "invalid fixture tag" >&2; exit 2 ;;
esac
out="$root/build/test-artifacts/dynamic-loader/$tag-$$"
rm -rf "$out"
mkdir -p "$out"

good_src="$root/test/fixtures/backend_plugin/dynamic_loader_provider_v1.c"
missing_src="$root/test/fixtures/backend_plugin/dynamic_loader_missing_symbol.c"

case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
        compiler='/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe'
        expected_sha='D43B7FA07B5B77B716E60600AD2792CFB2EEB370AECB6144BF6C698F2C6D7467'
        [ -x "$compiler" ] || { echo "missing exact LLVM 23.1.1 clang-cl" >&2; exit 3; }
        actual_sha=$(sha256sum "$compiler" | awk '{print toupper($1)}')
        [ "$actual_sha" = "$expected_sha" ] || { echo "clang-cl digest mismatch" >&2; exit 4; }
        "$compiler" --version | grep -F 'clang version 23.1.1' >/dev/null || exit 5
        good="$out/provider-v1.dll"
        missing="$out/provider-missing.dll"
        good_win=$(cygpath -w "$good")
        missing_win=$(cygpath -w "$missing")
        good_src_win=$(cygpath -w "$good_src")
        missing_src_win=$(cygpath -w "$missing_src")
        MSYS2_ARG_CONV_EXCL='*'
        export MSYS2_ARG_CONV_EXCL
        "$compiler" /nologo /LD "$good_src_win" "/Fe:$good_win" /link /NOLOGO
        "$compiler" /nologo /LD "$missing_src_win" "/Fe:$missing_win" /link /NOLOGO
        ;;
    Darwin*)
        compiler=clang
        good="$out/provider-v1.dylib"
        missing="$out/provider-missing.dylib"
        "$compiler" -std=c11 -dynamiclib "$good_src" -o "$good"
        "$compiler" -std=c11 -dynamiclib "$missing_src" -o "$missing"
        ;;
    *)
        compiler=clang
        good="$out/provider-v1.so"
        missing="$out/provider-missing.so"
        "$compiler" -std=c11 -fPIC -shared "$good_src" -o "$good"
        "$compiler" -std=c11 -fPIC -shared "$missing_src" -o "$missing"
        ;;
esac

[ -s "$good" ] && [ -s "$missing" ] || exit 6
case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
        good=$(cygpath -m "$good")
        missing=$(cygpath -m "$missing")
        ;;
esac
marker=$(dirname "$good")/unloaded.marker
printf 'FIXTURE_OK\nGOOD=%s\nMISSING=%s\nUNLOAD=%s\n' "$good" "$missing" "$marker"
