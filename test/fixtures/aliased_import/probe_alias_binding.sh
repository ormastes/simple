#!/bin/sh
# Object-level probe for
# doc/08_tracking/bug/aliased_import_shadowed_by_local_fn_native_codegen_2026-09-03.md
#
# Builds a two-module fixture on the seed's native-project lane and reports
# which function the aliased import actually bound to, read out of the ENTRY
# module's object file. Prints exactly three key=value lines; prints
# ENTRY_OBJECT=missing (and nothing else) when no object was produced, so a
# run that inspected nothing can never read as a pass.
#
# Usage: sh probe_alias_binding.sh <path-to-simple-binary>
set -e
BIN="$1"
[ -n "$BIN" ] || { echo "ENTRY_OBJECT=missing"; exit 0; }
T=$(mktemp -d)
printf 'pub fn probe() -> text:\n    "OTHER"\n' > "$T/other.spl"
printf 'use other.{probe as aliased_probe}\n\nfn probe() -> text:\n    "LOCAL"\n\nfn calls_alias() -> text:\n    aliased_probe()\n\nfn calls_local() -> text:\n    probe()\n\nfn main():\n    print(calls_alias())\n    print(calls_local())\n' > "$T/main.spl"
cd "$T"
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_KEEP_NATIVE_OBJS=1 "$BIN" \
  native-build --entry main.spl --source . -o main.exe > build.log 2>&1 || true
OBJ=$(grep -rla main__calls_local .simple 2>/dev/null | grep '[.]o$' | head -1)
if [ -z "$OBJ" ]; then echo ENTRY_OBJECT=missing; exit 0; fi
echo ENTRY_OBJECT=found
if grep -qa other__probe "$OBJ"; then echo ALIAS_TARGET=imported; else echo ALIAS_TARGET=local; fi
if grep -qa main__probe "$OBJ"; then echo LOCAL_SYMBOL=present; else echo LOCAL_SYMBOL=absent; fi
