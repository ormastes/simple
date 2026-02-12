#!/bin/sh
# Simple Language Compiler - FreeBSD wrapper
# Uses Linux compatibility layer (Linuxulator) to run the full compiler

# Ensure Linux compat is loaded
kldstat -q -m linux64 2>/dev/null || kldload linux64 2>/dev/null

# Run the Linux binary
exec /usr/local/simple/bin/simple-engine "$@"
