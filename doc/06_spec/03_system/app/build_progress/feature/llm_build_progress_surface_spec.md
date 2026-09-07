# LLM-Friendly Build Progress

The build manager maintains one current snapshot so an operator or LLM can answer “what is compiling, how much remains, did linking start, and what failed?” without reading a long log.

## Scenarios

1. A complete required-field snapshot survives encode/decode.
2. A stale writer cannot replace a live build.
3. Sequence or elapsed-time regression is rejected.
4. Build identity replacement is rejected even after a phase terminates; only the manager initializes a new build.
5. The concise reader reports counts, remaining work, ETA confidence, and link state in one line.

Detailed events remain append-only evidence and are not the reader API.
