# Simple lint parser failure returned clean — 2026-07-23

**Status:** SOURCE FIXED / PURE-SIMPLE QUALIFICATION PENDING

## Reproduction

Linting invalid Simple source such as `fn broken(` could emit a clean file
summary and exit 0 when no text-scanning rule matched the input.

## Root cause and fix

The CLI adapter used `parse_module_silent`, restored the shared parser error
state, then returned its existing text findings unchanged when parsing failed.
An empty text result therefore looked clean.

Parser failure now adds one unconditional PARSE001 deny diagnostic before the
adapter returns. The focused contract requires exactly one diagnostic at line 1
and proves both clean and pre-existing parser error state are restored.

A fresh pure-Simple Stage 4 CLI must run the focused contract and public JSONL
lint smoke before qualification.
