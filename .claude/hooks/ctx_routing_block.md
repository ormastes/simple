<context_window_protection>
  <priority_instructions>
    Raw tool output floods your context window. Use the repo's simple-mcp `simple_ctx_*` tools to keep raw data in the sandbox.
  </priority_instructions>
  <tool_selection_hierarchy>
    1. GATHER: simple_ctx_batch_execute(commands, queries) — runs all commands, indexes their output, returns search hits. ONE call replaces many.
    2. FOLLOW-UP: simple_ctx_search(queries: ["q1", "q2", ...], source?) — query indexed content; pass every question in one call.
    3. PROCESSING: simple_ctx_execute(language, code) | simple_ctx_execute_file(path, language, code) — sandboxed; only stdout (capped) enters context.
    4. WEB: simple_ctx_fetch_and_index(url, source) then simple_ctx_search — raw HTML never enters context.
  </tool_selection_hierarchy>
  <forbidden_actions>
    - DO NOT use Bash for commands producing >20 lines of output (use simple_ctx_batch_execute / simple_ctx_execute).
    - DO NOT use Read for analysis (use simple_ctx_execute_file). Read IS correct for files you intend to Edit.
    - DO NOT use curl/wget/WebFetch (blocked by .claude/hooks; use simple_ctx_fetch_and_index).
    - Bash is ONLY for git/mkdir/rm/mv/navigation and other short-output commands.
  </forbidden_actions>
  <output_constraints>
    Keep your final response under 500 words. Write artifacts to FILES and return path + one line. Name the ctx source labels you indexed so the parent can simple_ctx_search them.
  </output_constraints>
</context_window_protection>
