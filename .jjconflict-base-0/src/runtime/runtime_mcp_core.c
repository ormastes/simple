#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int64_t rt_stdin_read_mcp_message_text(void) {
    char line[4096];
    int64_t content_length = 0;

    while (fgets(line, sizeof(line), stdin)) {
        if (line[0] == '{') {
            size_t len = strlen(line);
            while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) len--;
            return rt_string_new((const uint8_t*)line, (int64_t)len);
        }

        if (line[0] == '\r' || line[0] == '\n') {
            if (content_length > 0) break;
            continue;
        }

        const char* prefix = "Content-Length:";
        size_t prefix_len = strlen(prefix);
        if (strncmp(line, prefix, prefix_len) == 0) {
            const char* p = line + prefix_len;
            while (*p == ' ' || *p == '\t') p++;
            content_length = strtoll(p, NULL, 10);
        }
    }

    if (content_length <= 0) return rt_string_new(NULL, 0);
    char* body = (char*)malloc((size_t)content_length);
    if (!body) return rt_string_new(NULL, 0);
    size_t n = fread(body, 1, (size_t)content_length, stdin);
    int64_t value = rt_string_new((const uint8_t*)body, (int64_t)n);
    free(body);
    return value;
}

int64_t rt_mcp_initialize_response_text(int64_t message) {
    int64_t len = rt_string_len(message);
    if (len <= 0) return rt_string_new(NULL, 0);
    const char* raw = (const char*)rt_string_data(message);
    if (!raw) return rt_string_new(NULL, 0);
    char* data = (char*)malloc((size_t)len + 1);
    if (!data) return rt_string_new(NULL, 0);
    memcpy(data, raw, (size_t)len);
    data[len] = '\0';
    int is_initialize = strstr(data, "\"method\":\"initialize\"") || strstr(data, "\"method\": \"initialize\"");
    int is_tools_list = strstr(data, "\"method\":\"tools/list\"") || strstr(data, "\"method\": \"tools/list\"");
    if (!is_initialize && !is_tools_list) {
        free(data);
        return rt_string_new(NULL, 0);
    }

    char id_buf[128];
    strcpy(id_buf, "null");
    const char* id_key = strstr(data, "\"id\"");
    if (id_key) {
        const char* p = id_key + 4;
        const char* end = data + len;
        while (p < end && (*p == ' ' || *p == '\t' || *p == ':')) p++;
        if (p < end && *p == '"') {
            const char* start = p++;
            size_t id_len = 0;
            while (p < end && *p != '"' && id_len + 2 < sizeof(id_buf)) {
                p++;
                id_len++;
            }
            if (p < end && *p == '"') {
                size_t total = (size_t)(p - start + 1);
                if (total >= sizeof(id_buf)) total = sizeof(id_buf) - 1;
                memcpy(id_buf, start, total);
                id_buf[total] = '\0';
            }
        } else {
            const char* start = p;
            while (p < end && *p != ',' && *p != '}' && *p != ' ' && *p != '\t' && *p != '\r' && *p != '\n') p++;
            size_t total = (size_t)(p - start);
            if (total > 0) {
                if (total >= sizeof(id_buf)) total = sizeof(id_buf) - 1;
                memcpy(id_buf, start, total);
                id_buf[total] = '\0';
            }
        }
    }

    const char* prefix = "{\"jsonrpc\":\"2.0\",\"id\":";
    const char* init_suffix = ",\"result\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{\"tools\":{\"listChanged\":true},\"resources\":{\"subscribe\":true,\"listChanged\":true},\"prompts\":{\"listChanged\":true},\"logging\":{},\"completions\":{},\"roots\":{\"listChanged\":false}},\"instructions\":\"Full-featured MCP server with table-driven tool dispatch. ~100 tools available (CLI passthrough + in-process handlers). Long-running tools return task handles for async polling.\",\"serverInfo\":{\"name\":\"simple-mcp-full\",\"version\":\"4.0.0\"}}}";
    const char* tools_suffix = ",\"result\":{\"tools\":["
        "{\"name\":\"debug_create_session\",\"description\":\"debug_create_session\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"debug_set_data_breakpoint\",\"description\":\"debug_set_data_breakpoint\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_read\",\"description\":\"simple_read\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_check\",\"description\":\"simple_check\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_symbols\",\"description\":\"simple_symbols\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_status\",\"description\":\"simple_status\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_diagnostics\",\"description\":\"simple_diagnostics\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_edit\",\"description\":\"simple_edit\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_multi_edit\",\"description\":\"simple_multi_edit\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_run\",\"description\":\"simple_run\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_test\",\"description\":\"simple_test\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_build\",\"description\":\"simple_build\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_format\",\"description\":\"simple_format\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_lint\",\"description\":\"simple_lint\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_fix\",\"description\":\"simple_fix\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}},"
        "{\"name\":\"simple_search\",\"description\":\"simple_search\",\"inputSchema\":{\"type\":\"object\",\"properties\":{},\"required\":[]}}"
        "]}}";
    const char* suffix = is_initialize ? init_suffix : tools_suffix;
    size_t out_len = strlen(prefix) + strlen(id_buf) + strlen(suffix);
    char* out = (char*)malloc(out_len + 1);
    if (!out) {
        free(data);
        return rt_string_new(NULL, 0);
    }
    memcpy(out, prefix, strlen(prefix));
    memcpy(out + strlen(prefix), id_buf, strlen(id_buf));
    memcpy(out + strlen(prefix) + strlen(id_buf), suffix, strlen(suffix));
    out[out_len] = '\0';
    int64_t value = rt_string_new((const uint8_t*)out, (int64_t)out_len);
    free(out);
    free(data);
    return value;
}

void rt_mcp_write_framed_text(int64_t body) {
    int64_t len = rt_string_len(body);
    const char* data = (const char*)rt_string_data(body);
    if (len < 0 || !data) {
        len = 0;
        data = "";
    }
    fprintf(stdout, "Content-Length: %lld\r\n\r\n", (long long)len);
    if (len > 0) fwrite(data, 1, (size_t)len, stdout);
    fflush(stdout);
}
