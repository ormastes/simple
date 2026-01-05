#!/bin/bash
# Git-to-JJ wrapper - Redirects git commands to jj equivalents
# This helps LLMs use jj instead of git

cmd="$1"
shift

echo "NOTE: This project uses jj (Jujutsu) instead of git."
echo "      Please use 'jj' commands directly next time."
echo "      Translating 'git $cmd' -> jj equivalent..."
echo ""

case "$cmd" in
    status)
        jj status "$@"
        ;;
    diff)
        jj diff "$@"
        ;;
    log)
        jj log "$@"
        ;;
    add)
        echo "Note: jj auto-tracks files, no need to add"
        jj status
        ;;
    commit)
        # Parse -m flag
        if [[ "$1" == "-m" ]]; then
            shift
            jj commit -m "$@"
        else
            jj commit "$@"
        fi
        ;;
    push)
        jj git push "$@"
        ;;
    pull|fetch)
        jj git fetch "$@"
        ;;
    checkout)
        jj edit "$@"
        ;;
    branch)
        jj bookmark "$@"
        ;;
    stash)
        echo "Note: jj doesn't need stash - changes are always preserved"
        jj status
        ;;
    init)
        jj git init "$@"
        ;;
    clone)
        jj git clone "$@"
        ;;
    show)
        jj show "$@"
        ;;
    reset)
        echo "Note: use 'jj restore' or 'jj abandon' instead of git reset"
        jj status
        ;;
    *)
        echo "Unknown git command: $cmd"
        echo "Use jj directly. Common commands:"
        echo "  jj status, jj diff, jj log, jj commit, jj describe"
        echo "  jj git push, jj git fetch, jj edit, jj new"
        exit 1
        ;;
esac
