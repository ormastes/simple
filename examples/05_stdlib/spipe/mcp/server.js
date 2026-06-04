#!/usr/bin/env node
import { existsSync, readFileSync, readdirSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const moduleRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");
let buffer = "";

function text(content) {
  return { content: [{ type: "text", text: content }] };
}

function listDirs(root) {
  const abs = join(moduleRoot, root);
  if (!existsSync(abs)) return [];
  return readdirSync(abs, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => entry.name)
    .sort();
}

const tools = [
  {
    name: "spipe_info",
    description: "Return SPipe module paths and link surfaces.",
    inputSchema: { type: "object", properties: {} }
  },
  {
    name: "spipe_experts",
    description: "List project, domain, and tool experts packaged with SPipe.",
    inputSchema: { type: "object", properties: {} }
  },
  {
    name: "spipe_read_doc",
    description: "Read a whitelisted SPipe document by relative path.",
    inputSchema: {
      type: "object",
      properties: {
        path: { type: "string", description: "Relative path under the SPipe module." }
      },
      required: ["path"]
    }
  },
  {
    name: "spipe_fine_tune_guide",
    description: "Read the SPipe LLM fine-tune process guide.",
    inputSchema: { type: "object", properties: {} }
  },
  {
    name: "spipe_fine_tune_model_guide",
    description: "Read the SPipe LLM model research and architecture guide.",
    inputSchema: { type: "object", properties: {} }
  },
  {
    name: "spipe_fine_tune_template",
    description: "Read the SPipe LLM fine-tune attempt record template.",
    inputSchema: { type: "object", properties: {} }
  }
];

function readDoc(path) {
  if (!path || path.includes("..") || path.startsWith("/") || path.startsWith("\\")) {
    throw new Error("path must be a relative path inside the SPipe module");
  }
  const allowed = [
    "README.md",
    "doc/00_llm_process/spipe/",
    "doc/00_llm_process/project_expert/",
    "doc/00_llm_process/domain_expert/",
    "doc/00_llm_process/tool_expert/",
    "doc/00_llm_process/template/"
  ];
  if (!allowed.some((prefix) => path === prefix || path.startsWith(prefix))) {
    throw new Error("path is outside the SPipe documentation allowlist");
  }
  const abs = join(moduleRoot, path);
  if (!existsSync(abs)) throw new Error(`document not found: ${path}`);
  return readFileSync(abs, "utf8");
}

function handleTool(name, args = {}) {
  if (name === "spipe_info") {
    return text([
      `module=${moduleRoot}`,
      "surface=doc/00_llm_process/skill_command",
      "surface=doc/00_llm_process/spipe",
      "surface=doc/00_llm_process/template",
      "surface=doc/00_llm_process/project_expert",
      "surface=doc/00_llm_process/domain_expert",
      "surface=doc/00_llm_process/tool_expert"
    ].join("\n"));
  }
  if (name === "spipe_experts") {
    return text([
      `project_expert=${listDirs("doc/00_llm_process/project_expert").join(",")}`,
      `domain_expert=${listDirs("doc/00_llm_process/domain_expert").join(",")}`,
      `tool_expert=${listDirs("doc/00_llm_process/tool_expert").join(",")}`
    ].join("\n"));
  }
  if (name === "spipe_read_doc") {
    return text(readDoc(args.path));
  }
  if (name === "spipe_fine_tune_guide") {
    return text(readDoc("doc/00_llm_process/spipe/llm_finetune.md"));
  }
  if (name === "spipe_fine_tune_model_guide") {
    return text(readDoc("doc/00_llm_process/spipe/llm_model_research.md"));
  }
  if (name === "spipe_fine_tune_template") {
    return text(readDoc("doc/00_llm_process/spipe/llm_finetune_attempt_template.sdn"));
  }
  throw new Error(`unknown tool: ${name}`);
}

function response(id, result) {
  process.stdout.write(`${JSON.stringify({ jsonrpc: "2.0", id, result })}\n`);
}

function errorResponse(id, error) {
  process.stdout.write(`${JSON.stringify({
    jsonrpc: "2.0",
    id,
    error: { code: -32000, message: error.message || String(error) }
  })}\n`);
}

function handle(message) {
  if (message.method === "initialize") {
    response(message.id, {
      protocolVersion: "2024-11-05",
      capabilities: { tools: {}, resources: {} },
      serverInfo: { name: "spipe", version: "0.1.0" }
    });
    return;
  }
  if (message.method === "tools/list") {
    response(message.id, { tools });
    return;
  }
  if (message.method === "tools/call") {
    const params = message.params || {};
    response(message.id, handleTool(params.name, params.arguments || {}));
    return;
  }
  if (message.method === "resources/list") {
    response(message.id, {
      resources: [
        {
          uri: "spipe://skill",
          name: "SPipe Skill",
          mimeType: "text/markdown",
          description: "Canonical SPipe skill guide."
        }
      ]
    });
    return;
  }
  if (message.method === "resources/read") {
    const uri = message.params?.uri;
    if (uri !== "spipe://skill") throw new Error(`unknown resource: ${uri}`);
    response(message.id, {
      contents: [{
        uri,
        mimeType: "text/markdown",
        text: readDoc("doc/00_llm_process/spipe/skill.md")
      }]
    });
    return;
  }
  if (message.id !== undefined) response(message.id, {});
}

process.stdin.setEncoding("utf8");
process.stdin.on("data", (chunk) => {
  buffer += chunk;
  let newline;
  while ((newline = buffer.indexOf("\n")) >= 0) {
    const line = buffer.slice(0, newline).trim();
    buffer = buffer.slice(newline + 1);
    if (!line) continue;
    try {
      handle(JSON.parse(line));
    } catch (error) {
      errorResponse(null, error);
    }
  }
});
