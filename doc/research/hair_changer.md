# Hair Changer — Research

**Feature:** doc/requirement/hair_changer.md
**Date:** 2026-03-15

## Codebase Findings

### HTTP Server (Built-in)
Simple runtime has full HTTP server support:
- `rt_http_server_create(port)` — create server on port
- `rt_http_server_route(server, method, path, handler)` — register routes
- `rt_http_server_static(server, path, dir)` — serve static files
- `rt_http_server_start(server)` — start listening
- `rt_http_response_create(status, body)` — create responses
- `rt_http_response_set_header(resp, key, val)` — set headers
- `rt_http_response_json(resp, json)` — JSON response
- `rt_http_request_body(req)` — read request body
- `rt_http_request_query(req, key)` — query params

Reference: `src/lib/nogc_sync_mut/io/http_ffi.spl`
Working example: `src/app/web_dashboard/server.spl`

### I18n (Built-in)
- `rt_i18n_get_message(domain, id, ctx_handle)` — domain+ID lookup
- `rt_i18n_context_new/insert/free` — interpolation contexts
- Reference: `src/lib/common/diagnostics/i18n_context.spl`

### Gemini Provider (Existing)
- CLI: `gemini --sandbox off -p <prompt> --output-format json`
- HTTP: `https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-flash-image:generateContent`
- Multi-image: base64-encoded images in `inline_data` parts
- Response: `responseModalities: ["TEXT", "IMAGE"]`
- Cost: ~$0.039/image

### File I/O
- `rt_file_read_bytes(path)` / `rt_file_write_bytes(path, data)`
- `rt_dir_create_all(path)` — recursive mkdir
- `rt_file_exists(path)` — existence check

### Process Execution
- `rt_process_run(cmd, args)` → `(stdout, stderr, exit_code)`
- Can call `gemini` CLI as subprocess with image file args

## External Research

### Gemini 2.5 Flash Image API
- Model ID: `gemini-2.5-flash-image` (or `gemini-2.5-flash-preview-image-generation`)
- Endpoint: `POST https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent`
- Multi-image input: Include multiple `inline_data` parts with base64 + MIME type
- Config: `generationConfig: { responseModalities: ["TEXT", "IMAGE"] }`
- Supports: style transfer, image editing, multi-image composition
- Character consistency across edits

### Hair Style Transfer Approach
Best approach with Gemini 2.5:
1. Send face photo (base64) + hair reference photo (base64)
2. Prompt: "Apply the hairstyle from the second image to the person in the first image. Keep the face identical. [options from checkboxes]"
3. Receive generated image in response

### Web UI Approach
- Simple serves static HTML/CSS/JS via `rt_http_server_static`
- API endpoints for image upload and generation
- Frontend uses fetch() to call backend API
- Base64 encoding in browser via FileReader API

## Risks

1. **Gemini API rate limits** — may need throttling for concurrent users
2. **Image size** — base64 doubles size, large images may hit API limits
3. **Quality variance** — Gemini may not always preserve face identity perfectly
4. **i18n complexity** — frontend i18n simpler with JSON translation files vs runtime FFI

## Recommendations

1. Use **static HTML/CSS/JS** frontend served by Simple HTTP server
2. Use **Gemini CLI** for simplest integration (vs raw HTTP API)
3. Use **JSON translation files** for frontend i18n (simpler than runtime i18n FFI)
4. Store presets as **SDN files** in a gallery/ directory
5. Implement **before/after slider** using pure CSS + JS (no framework needed)
