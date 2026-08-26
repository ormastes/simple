import { existsSync, readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";

export const tools = Object.freeze([
  { name: "spipe_info", description: "Return SPipe module paths and link surfaces.", inputSchema: { type: "object", properties: {} } },
  { name: "spipe_experts", description: "List project, domain, and tool experts packaged with SPipe.", inputSchema: { type: "object", properties: {} } },
  {
    name: "spipe_read_doc",
    description: "Read a whitelisted SPipe document by relative path.",
    inputSchema: {
      type: "object",
      properties: { path: { type: "string", description: "Relative path under the SPipe module." } },
      required: ["path"]
    }
  },
  { name: "spipe_fine_tune_guide", description: "Read the SPipe LLM fine-tune process guide.", inputSchema: { type: "object", properties: {} } },
  { name: "spipe_fine_tune_model_guide", description: "Read the SPipe LLM model research and architecture guide.", inputSchema: { type: "object", properties: {} } },
  { name: "spipe_fine_tune_template", description: "Read the SPipe LLM fine-tune attempt record template.", inputSchema: { type: "object", properties: {} } },
  { name: "spipe_release_guide", description: "Read the canonical protected software-release and beta-backport guide.", inputSchema: { type: "object", properties: {} } },
  { name: "spipe_release_capabilities", description: "Return declared release/session/candidate schemas and safe planning capabilities.", inputSchema: { type: "object", properties: {} } }
]);

function text(content) {
  return { content: [{ type: "text", text: content }] };
}

function listDirs(moduleRoot, root) {
  const abs = join(moduleRoot, root);
  if (!existsSync(abs)) return [];
  return readdirSync(abs, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => entry.name)
    .sort();
}

export function readDoc(moduleRoot, path) {
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

export function callTool(moduleRoot, name, args = {}) {
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
      `project_expert=${listDirs(moduleRoot, "doc/00_llm_process/project_expert").join(",")}`,
      `domain_expert=${listDirs(moduleRoot, "doc/00_llm_process/domain_expert").join(",")}`,
      `tool_expert=${listDirs(moduleRoot, "doc/00_llm_process/tool_expert").join(",")}`
    ].join("\n"));
  }
  if (name === "spipe_read_doc") return text(readDoc(moduleRoot, args.path));
  if (name === "spipe_fine_tune_guide") return text(readDoc(moduleRoot, "doc/00_llm_process/spipe/llm_finetune.md"));
  if (name === "spipe_fine_tune_model_guide") return text(readDoc(moduleRoot, "doc/00_llm_process/spipe/llm_model_research.md"));
  if (name === "spipe_fine_tune_template") return text(readDoc(moduleRoot, "doc/00_llm_process/spipe/llm_finetune_attempt_template.sdn"));
  if (name === "spipe_release_guide") return text(readDoc(moduleRoot, "doc/00_llm_process/skill_command/command/release.md"));
  if (name === "spipe_release_capabilities") return text([
    "vcs_policy=spipe-vcs/3",
    "session=spipe-session/1",
    "release=spipe-release/1",
    "candidate=spipe-candidate/1",
    "isolated_sessions=true",
    "reviewed_beta_backports=true",
    "immutable_release_candidates=true",
    "promote_without_rebuild=true"
  ].join("\n"));
  throw new Error(`unknown tool: ${name}`);
}
