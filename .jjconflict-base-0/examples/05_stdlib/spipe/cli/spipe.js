#!/usr/bin/env node
import { appendFileSync, chmodSync, existsSync, lstatSync, mkdirSync, readlinkSync, readdirSync, readFileSync, rmSync, symlinkSync, unlinkSync, writeFileSync } from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const moduleRoot = resolve(dirname(fileURLToPath(import.meta.url)), "..");

function printUsage() {
  console.log(`Usage: spipe <command> [args]

Commands:
  info                 Print module paths and available surfaces.
  experts              List project, tool, and domain experts.
  link-plan [host]     Show host links that setup will manage.
  doc-root [host]      Print configured host process-doc root.
  doc-link [host] [doc-root]
                       Create or update host .spipe/doc link.
  doctor [host]        Check module files and host link status.
  skill                Print the SPipe skill guide.
  fine-tune-guide      Print the LLM fine-tune process guide.
  fine-tune-model-guide
                       Print the LLM base-model research guide.
  fine-tune-template   Print the LLM fine-tune attempt template.
  fine-tune-init       Initialize host fine-tune state directories and registries.
  fine-tune-new-attempt <attempt_id> <goal> [target]
                       Create a host attempt record from the template.
  fine-tune-record-data <attempt_id> <name> <source> <license> <download_command> <cache_path> [checksum]
                       Append data-download evidence for an attempt.
  fine-tune-data-plan <attempt_id>
                       Print recorded data downloads and verification checks.
  fine-tune-record-data-check <attempt_id> <name> <cache_path> <result> [checksum] [notes]
                       Append data cache/checksum verification evidence.
  fine-tune-record-model <attempt_id> <base_model> <revision> <reason> <deployment_target>
                       Append base-model selection evidence for an attempt.
  fine-tune-record-model-research <attempt_id> <candidate_model> <license> <context_length> <fit> <constraints> <decision>
                       Append candidate model research evidence.
  fine-tune-record-model-arch <attempt_id> <architecture_doc> <model_family> <data_strategy> <training_strategy> <deployment_target> <fallback>
                       Append new-model architecture evidence.
  fine-tune-scaffold-model-arch <attempt_id> <architecture_doc> <model_family> <data_strategy> <training_strategy> <deployment_target> <fallback>
                       Write a new-model architecture doc scaffold and record it.
  fine-tune-record-method <attempt_id> <method> <reason> <fallback> <selected_by>
                       Append tuning-method selection evidence.
  fine-tune-model-method-options <attempt_id>
                       List researched model candidates and supported tuning methods.
  fine-tune-select-model-method <attempt_id> <base_model> <revision> <deployment_target> <method> <selected_by> <fallback> [reason]
                       Record base-model and tuning-method design choices.
  fine-tune-record-training <attempt_id> <method> <training_script> <training_command> <model_artifact>
                       Append tuning/training evidence for an attempt.
  fine-tune-scaffold-training <attempt_id> <method> <script_path> [model_artifact]
                       Write an executable training-script scaffold and record it.
  fine-tune-record-eval <attempt_id> <eval_command> <metrics> <target> <result>
                       Append evaluation evidence for an attempt.
  fine-tune-record-decision <attempt_id> <status> <retry_target> [next_attempt] [notes]
                       Append verify-loop decision evidence for an attempt.
  fine-tune-record-verify-loop <attempt_id> <eval_command> <metrics> <target> <result> <status> <retry_target> [next_attempt] [notes]
                       Append eval+decision evidence and optionally create retry attempt.
  fine-tune-record-process <attempt_id> <research_doc> <requirements_doc> <nfr_doc> <plan_doc> <architecture_doc> <design_doc>
                       Append pipeline document trace for an attempt.
  fine-tune-scaffold-process-docs <attempt_id> <feature_slug> [title]
                       Write research/requirements/plan/design doc scaffolds and record them.
  fine-tune-record-requirements <attempt_id> <feature_option> <nfr_option> <selected_by> <selection_doc> [notes]
                       Append requirement option selection evidence.
  fine-tune-options    List host fine-tune requirement options.
  fine-tune-select-requirements <attempt_id> <feature_option> <nfr_option> <selected_by> [notes]
                       Write final requirement docs and record selected options.
  fine-tune-record-app <attempt_id> <app_target> <usage> <handoff_doc>
                       Append LLM-backed app/server handoff evidence.
  fine-tune-record-retune <attempt_id> <reason> <source_eval> <next_attempt> <retry_target>
                       Append retune request evidence from verification.
  fine-tune-create-retry <source_attempt_id> <next_attempt_id> [goal] [target]
                       Create a retry attempt from a failed verification decision.
  fine-tune-app-handoff <attempt_id>
                       Print LLM-backed app/server handoff and retune evidence.
  fine-tune-status <attempt_id>
                       Report attempt evidence across host registries.
  fine-tune-doctor <attempt_id>
                       Check attempt evidence quality, placeholders, and next action.
  fine-tune-ready <attempt_id>
                       Fail unless an attempt is ready for real training/use.
  fine-tune-next <attempt_id>
                       Print the next fine-tune phase required by readiness.
  fine-tune-report <attempt_id>
                       Print a consolidated attempt evidence report.
  fine-tune-verify <record.sdn>
                       Verify required fields in an attempt record.
`);
}

function rel(path) {
  return path.replace(`${moduleRoot}/`, "");
}

function listDirs(root) {
  const abs = join(moduleRoot, root);
  if (!existsSync(abs)) return [];
  return readdirSync(abs, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => entry.name)
    .sort();
}

const surfaceNames = [
  "skill_command",
  "spipe",
  "template",
  "project_expert",
  "domain_expert",
  "tool_expert"
];

function linkPlan(hostRoot = resolve(moduleRoot, "..", "..")) {
  const root = resolve(hostRoot);
  const docRoot = readConfiguredDocRoot(root);
  return surfaceNames.map((surface) => ({
    surface: `${docRoot}/${surface}`,
    source: join(moduleRoot, "doc/00_llm_process", surface),
    target: join(root, docRoot, surface)
  }));
}

function commandInfo() {
  console.log(`spipe_module=${moduleRoot}`);
  console.log(`spipe_skill=${join(moduleRoot, "doc/00_llm_process/spipe/skill.md")}`);
  for (const surface of surfaceNames) {
    console.log(`surface=doc/00_llm_process/${surface}`);
  }
}

function commandExperts() {
  const roots = {
    project_expert: "doc/00_llm_process/project_expert",
    domain_expert: "doc/00_llm_process/domain_expert",
    tool_expert: "doc/00_llm_process/tool_expert"
  };
  for (const [name, root] of Object.entries(roots)) {
    const dirs = listDirs(root);
    console.log(`${name}=${dirs.length ? dirs.join(",") : "(none)"}`);
  }
}

function commandLinkPlan(hostRoot) {
  for (const item of linkPlan(hostRoot)) {
    console.log(`${item.surface}`);
    console.log(`  source=${item.source}`);
    console.log(`  target=${item.target}`);
  }
}

function readConfiguredDocRoot(hostRoot) {
  const configPath = join(resolve(hostRoot), ".spipe/config.sdn");
  if (!existsSync(configPath)) return "doc/llm_process";
  const content = readFileSync(configPath, "utf8");
  const match = content.match(/^\s*host_process_doc:\s*([^\s#]+)\s*$/m);
  return match ? match[1] : "doc/llm_process";
}

function commandDocRoot(hostRoot = resolve(moduleRoot, "..", "..")) {
  console.log(readConfiguredDocRoot(hostRoot));
}

function commandDocLink(hostRoot = resolve(moduleRoot, "..", ".."), docRoot) {
  const root = resolve(hostRoot);
  const configuredDocRoot = docRoot || readConfiguredDocRoot(root);
  const docAbs = join(root, configuredDocRoot);
  const linkPath = join(root, ".spipe/doc");

  if (!existsSync(docAbs)) {
    console.error(`spipe doc-link: doc root does not exist: ${configuredDocRoot}`);
    process.exitCode = 1;
    return;
  }

  mkdirSync(dirname(linkPath), { recursive: true });
  const nextTarget = relative(dirname(linkPath), docAbs);
  if (existsSync(linkPath) || lstatSync(dirname(linkPath)).isDirectory()) {
    if (existsSync(linkPath)) {
      const stat = lstatSync(linkPath);
      if (!stat.isSymbolicLink()) {
        console.error(`spipe doc-link: refusing to replace non-symlink: ${linkPath}`);
        process.exitCode = 1;
        return;
      }
      const current = readlinkSync(linkPath);
      if (current === nextTarget) {
        console.log(`doc_link=ok ${linkPath} -> ${current}`);
        return;
      }
      unlinkSync(linkPath);
    }
  }

  symlinkSync(nextTarget, linkPath);
  console.log(`doc_link=linked ${linkPath} -> ${nextTarget}`);
}

function commandDoctor(hostRoot) {
  const root = resolve(hostRoot || resolve(moduleRoot, "..", ".."));
  let failures = 0;
  for (const surface of surfaceNames) {
    const source = join(moduleRoot, "doc/00_llm_process", surface);
    if (!existsSync(source)) {
      failures += 1;
      console.log(`missing_source doc/00_llm_process/${surface}`);
    } else {
      console.log(`source_ok doc/00_llm_process/${surface}`);
    }
  }

  for (const item of linkPlan(hostRoot)) {
    if (!existsSync(item.target)) {
      console.log(`target_missing ${item.surface}`);
      continue;
    }
    const stat = lstatSync(item.target);
    const kind = stat.isSymbolicLink() ? "link" : stat.isDirectory() ? "directory" : "file";
    console.log(`target_${kind} ${item.surface}`);
  }

  const docRoot = readConfiguredDocRoot(root);
  const docLink = join(root, ".spipe/doc");
  const docTarget = relative(dirname(docLink), join(root, docRoot));
  const hostChecks = [
    ["compatibility_submodule", join(root, ".spipe/spipe"), "exists"],
    ["example_project_submodule", join(root, "examples/spipe"), "exists"],
    ["spipe_project_link", join(root, ".spipe/spipe_project"), relative(join(root, ".spipe"), join(root, "examples/spipe"))],
    ["doc_link", docLink, docTarget],
    ["domain_expert_link", join(root, ".spipe/domain_expert"), relative(join(root, ".spipe"), join(root, "examples/spipe/doc/00_llm_process/domain_expert"))],
    ["template_link", join(root, ".spipe/template"), relative(join(root, ".spipe"), join(root, "examples/spipe/doc/00_llm_process/template"))],
    ["spipe_docs_link", join(root, ".spipe/spipe_docs"), relative(join(root, ".spipe"), join(root, "examples/spipe/doc/00_llm_process/spipe"))],
    ["project_expert_spipe_link", join(root, ".spipe/project_expert/spipe"), relative(join(root, ".spipe/project_expert"), join(root, "examples/spipe/doc/00_llm_process/project_expert/simple"))],
    ["tool_expert_spipe_link", join(root, ".spipe/tool_expert/spipe_submodule"), relative(join(root, ".spipe/tool_expert"), join(root, "examples/spipe/doc/00_llm_process/tool_expert/spipe_submodule"))]
  ];
  for (const [name, path, expected] of hostChecks) {
    if (!existsSync(path)) {
      failures += 1;
      console.log(`host_missing ${name} ${path}`);
      continue;
    }
    const stat = lstatSync(path);
    if (expected !== "exists") {
      if (!stat.isSymbolicLink()) {
        failures += 1;
        console.log(`host_not_link ${name} ${path}`);
        continue;
      }
      const current = readlinkSync(path);
      if (current !== expected) {
        failures += 1;
        console.log(`host_bad_link ${name} expected=${expected} actual=${current}`);
        continue;
      }
    }
    console.log(`host_ok ${name}`);
  }

  console.log(failures === 0 ? "spipe_doctor=pass" : `spipe_doctor=fail missing=${failures}`);
  process.exitCode = failures === 0 ? 0 : 1;
}

function commandSkill() {
  const path = join(moduleRoot, "doc/00_llm_process/spipe/skill.md");
  process.stdout.write(readFileSync(path, "utf8"));
}

function readQuotedValue(content, key) {
  const escaped = key.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const matches = [...content.matchAll(new RegExp(`^\\s*${escaped}:\\s*"([^"]*)"\\s*$`, "gm"))];
  return matches.length ? matches[matches.length - 1][1] : "";
}

function commandFineTuneGuide() {
  const path = join(moduleRoot, "doc/00_llm_process/spipe/llm_finetune.md");
  process.stdout.write(readFileSync(path, "utf8"));
}

function commandFineTuneModelGuide() {
  const path = join(moduleRoot, "doc/00_llm_process/spipe/llm_model_research.md");
  process.stdout.write(readFileSync(path, "utf8"));
}

function commandFineTuneTemplate() {
  const path = join(moduleRoot, "doc/00_llm_process/spipe/llm_finetune_attempt_template.sdn");
  process.stdout.write(readFileSync(path, "utf8"));
}

function writeIfMissing(path, content) {
  if (!existsSync(path)) {
    writeFileSync(path, content);
  }
}

function commandFineTuneInit() {
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const attemptsDir = join(root, "attempts");
  const scriptsDir = join(root, "scripts");
  mkdirSync(attemptsDir, { recursive: true });
  mkdirSync(scriptsDir, { recursive: true });

  const template = readFileSync(join(moduleRoot, "doc/00_llm_process/spipe/llm_finetune_attempt_template.sdn"), "utf8");
  writeIfMissing(join(attemptsDir, "template.sdn"), template);
  writeIfMissing(join(root, "attempts.sdn"), "# Attempt index for SPipe LLM fine-tune process.\n\nattempts: []\n");
  writeIfMissing(join(root, "data_downloads.sdn"), "# Data download evidence for SPipe LLM fine-tune attempts.\n\ndata_downloads:\n");
  writeIfMissing(join(root, "data_checks.sdn"), "# Data cache/checksum verification evidence for SPipe LLM fine-tune attempts.\n\ndata_checks:\n");
  writeIfMissing(join(root, "process_docs.sdn"), "# Pipeline document trace for SPipe LLM fine-tune attempts.\n\nprocess_docs:\n");
  writeIfMissing(join(root, "requirements_selection.sdn"), "# Requirement option selection evidence for SPipe LLM fine-tune attempts.\n\nrequirements_selection:\n");
  writeIfMissing(join(root, "model_research.sdn"), "# Candidate model research evidence for SPipe LLM fine-tune attempts.\n\nmodel_research:\n");
  writeIfMissing(join(root, "model_architecture.sdn"), "# New-model architecture evidence for SPipe LLM fine-tune attempts.\n\nmodel_architecture:\n");
  writeIfMissing(join(root, "tuning_methods.sdn"), "# Tuning-method selection evidence for SPipe LLM fine-tune attempts.\n\ntuning_methods:\n");
  writeIfMissing(join(root, "models.sdn"), "# Model selection evidence for SPipe LLM fine-tune attempts.\n\nmodels:\n");
  writeIfMissing(join(root, "training_scripts.sdn"), "# Training script evidence for SPipe LLM fine-tune attempts.\n\ntraining_scripts:\n");
  writeIfMissing(join(root, "eval_results.sdn"), "# Evaluation evidence for SPipe LLM fine-tune attempts.\n\neval_results:\n");
  writeIfMissing(join(root, "decisions.sdn"), "# Verification decision evidence for SPipe LLM fine-tune attempts.\n\ndecisions:\n");
  writeIfMissing(join(root, "app_handoffs.sdn"), "# LLM-backed app/server handoff evidence for SPipe fine-tune attempts.\n\napp_handoffs:\n");
  writeIfMissing(join(root, "retune_requests.sdn"), "# Retune request evidence for SPipe LLM-backed app/server loops.\n\nretune_requests:\n");
  console.log(`fine_tune_init=ok ${root}`);
}

function quoteSdn(value) {
  return String(value).replace(/\\/g, "\\\\").replace(/"/g, "\\\"");
}

function quoteShell(value) {
  return `'${String(value).replace(/'/g, `'\\''`)}'`;
}

function commandFineTuneNewAttempt(args) {
  const [attemptId, goal, target = ""] = args;
  if (!attemptId || !goal) {
    console.error("spipe fine-tune-new-attempt: attempt_id and goal are required");
    process.exitCode = 2;
    return;
  }
  if (!/^[A-Za-z0-9_.-]+$/.test(attemptId)) {
    console.error("spipe fine-tune-new-attempt: attempt_id may contain only letters, numbers, dot, dash, and underscore");
    process.exitCode = 2;
    return;
  }

  const hostRoot = process.cwd();
  const attemptsDir = join(hostRoot, ".spipe/llm-finetune-process/attempts");
  const outPath = join(attemptsDir, `${attemptId}.sdn`);
  if (existsSync(outPath)) {
    console.error(`spipe fine-tune-new-attempt: attempt already exists: ${outPath}`);
    process.exitCode = 1;
    return;
  }

  mkdirSync(attemptsDir, { recursive: true });
  let content = readFileSync(join(moduleRoot, "doc/00_llm_process/spipe/llm_finetune_attempt_template.sdn"), "utf8");
  content = content
    .replace('  attempt_id: ""', `  attempt_id: "${quoteSdn(attemptId)}"`)
    .replace('  goal: ""', `  goal: "${quoteSdn(goal)}"`)
    .replace('  app_or_server_target: ""', `  app_or_server_target: "${quoteSdn(target)}"`);
  writeFileSync(outPath, content);
  console.log(outPath);
}

function commandFineTuneRecordData(args) {
  const [attemptId, name, source, license, downloadCommand, cachePath, checksum = ""] = args;
  if (!attemptId || !name || !source || !license || !downloadCommand || !cachePath) {
    console.error("spipe fine-tune-record-data: attempt_id, name, source, license, download_command, and cache_path are required");
    process.exitCode = 2;
    return;
  }
  if (!/^[A-Za-z0-9_.-]+$/.test(attemptId)) {
    console.error("spipe fine-tune-record-data: attempt_id may contain only letters, numbers, dot, dash, and underscore");
    process.exitCode = 2;
    return;
  }

  const hostRoot = process.cwd();
  const root = join(hostRoot, ".spipe/llm-finetune-process");
  const registryPath = join(root, "data_downloads.sdn");
  mkdirSync(root, { recursive: true });
  if (!existsSync(registryPath)) {
    writeFileSync(registryPath, "# Data download evidence for SPipe LLM fine-tune attempts.\n\ndata_downloads:\n");
  }

  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    name: "${quoteSdn(name)}"
    source: "${quoteSdn(source)}"
    license: "${quoteSdn(license)}"
    download_command: "${quoteSdn(downloadCommand)}"
    cache_path: "${quoteSdn(cachePath)}"
    checksum: "${quoteSdn(checksum)}"
`);
  console.log(registryPath);
}

function commandFineTuneRecordDataCheck(args) {
  const [attemptId, name, cachePath, result, checksum = "", notes = ""] = args;
  if (!attemptId || !name || !cachePath || !result) {
    console.error("spipe fine-tune-record-data-check: attempt_id, name, cache_path, and result are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-data-check", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "data_checks.sdn", "# Data cache/checksum verification evidence for SPipe LLM fine-tune attempts.", "data_checks");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    name: "${quoteSdn(name)}"
    cache_path: "${quoteSdn(cachePath)}"
    result: "${quoteSdn(result)}"
    checksum: "${quoteSdn(checksum)}"
    notes: "${quoteSdn(notes)}"
`);
  console.log(registryPath);
}

function commandFineTuneDataPlan(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-data-plan: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-data-plan", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  console.log("data_downloads:");
  console.log(registryBlockForAttempt(root, "data_downloads.sdn", attemptId) || "  missing");
  console.log("data_checks:");
  console.log(registryBlockForAttempt(root, "data_checks.sdn", attemptId) || "  missing");
}

function initRegistry(root, fileName, header, rootKey) {
  const registryPath = join(root, fileName);
  mkdirSync(root, { recursive: true });
  if (!existsSync(registryPath)) {
    writeFileSync(registryPath, `${header}\n\n${rootKey}:\n`);
  }
  return registryPath;
}

function commandFineTuneRecordModel(args) {
  const [attemptId, baseModel, revision, reason, deploymentTarget] = args;
  if (!attemptId || !baseModel || !revision || !reason || !deploymentTarget) {
    console.error("spipe fine-tune-record-model: attempt_id, base_model, revision, reason, and deployment_target are required");
    process.exitCode = 2;
    return;
  }
  if (!/^[A-Za-z0-9_.-]+$/.test(attemptId)) {
    console.error("spipe fine-tune-record-model: attempt_id may contain only letters, numbers, dot, dash, and underscore");
    process.exitCode = 2;
    return;
  }
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "models.sdn", "# Model selection evidence for SPipe LLM fine-tune attempts.", "models");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    base_model: "${quoteSdn(baseModel)}"
    revision: "${quoteSdn(revision)}"
    reason: "${quoteSdn(reason)}"
    deployment_target: "${quoteSdn(deploymentTarget)}"
`);
  console.log(registryPath);
}

function commandFineTuneRecordModelResearch(args) {
  const [attemptId, candidateModel, license, contextLength, fit, constraints, decision] = args;
  if (!attemptId || !candidateModel || !license || !contextLength || !fit || !constraints || !decision) {
    console.error("spipe fine-tune-record-model-research: attempt_id, candidate_model, license, context_length, fit, constraints, and decision are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-model-research", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "model_research.sdn", "# Candidate model research evidence for SPipe LLM fine-tune attempts.", "model_research");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    candidate_model: "${quoteSdn(candidateModel)}"
    license: "${quoteSdn(license)}"
    context_length: "${quoteSdn(contextLength)}"
    fit: "${quoteSdn(fit)}"
    constraints: "${quoteSdn(constraints)}"
    decision: "${quoteSdn(decision)}"
`);
  console.log(registryPath);
}

function commandFineTuneRecordModelArch(args) {
  const [attemptId, architectureDoc, modelFamily, dataStrategy, trainingStrategy, deploymentTarget, fallback] = args;
  if (!attemptId || !architectureDoc || !modelFamily || !dataStrategy || !trainingStrategy || !deploymentTarget || !fallback) {
    console.error("spipe fine-tune-record-model-arch: attempt_id, architecture_doc, model_family, data_strategy, training_strategy, deployment_target, and fallback are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-model-arch", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "model_architecture.sdn", "# New-model architecture evidence for SPipe LLM fine-tune attempts.", "model_architecture");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    architecture_doc: "${quoteSdn(architectureDoc)}"
    model_family: "${quoteSdn(modelFamily)}"
    data_strategy: "${quoteSdn(dataStrategy)}"
    training_strategy: "${quoteSdn(trainingStrategy)}"
    deployment_target: "${quoteSdn(deploymentTarget)}"
    fallback: "${quoteSdn(fallback)}"
`);
  console.log(registryPath);
}

function modelArchDocBody(attemptId, modelFamily, dataStrategy, trainingStrategy, deploymentTarget, fallback) {
  return `# SPipe LLM Model Architecture: ${attemptId}

## Attempt

- Attempt ID: ${attemptId}
- Model family: ${modelFamily}
- Deployment target: ${deploymentTarget}

## Data Strategy

${dataStrategy}

## Training Strategy

${trainingStrategy}

## Architecture Notes

- Define tokenizer and context assumptions.
- Define adapter/new-model boundaries.
- Define app/server integration points.
- Define eval metrics that prove the architecture is fit for use.
- Define artifact naming and retention policy.

## Fallback

${fallback}
`;
}

function commandFineTuneScaffoldModelArch(args) {
  const [attemptId, architectureDoc, modelFamily, dataStrategy, trainingStrategy, deploymentTarget, fallback] = args;
  if (!attemptId || !architectureDoc || !modelFamily || !dataStrategy || !trainingStrategy || !deploymentTarget || !fallback) {
    console.error("spipe fine-tune-scaffold-model-arch: attempt_id, architecture_doc, model_family, data_strategy, training_strategy, deployment_target, and fallback are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-scaffold-model-arch", attemptId)) return;
  const outPath = resolve(process.cwd(), architectureDoc);
  mkdirSync(dirname(outPath), { recursive: true });
  writeFileSync(outPath, modelArchDocBody(attemptId, modelFamily, dataStrategy, trainingStrategy, deploymentTarget, fallback));
  commandFineTuneRecordModelArch([attemptId, architectureDoc, modelFamily, dataStrategy, trainingStrategy, deploymentTarget, fallback]);
  console.log(architectureDoc);
}

function commandFineTuneRecordMethod(args) {
  const [attemptId, method, reason, fallback, selectedBy] = args;
  if (!attemptId || !method || !reason || !fallback || !selectedBy) {
    console.error("spipe fine-tune-record-method: attempt_id, method, reason, fallback, and selected_by are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-method", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "tuning_methods.sdn", "# Tuning-method selection evidence for SPipe LLM fine-tune attempts.", "tuning_methods");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    method: "${quoteSdn(method)}"
    reason: "${quoteSdn(reason)}"
    fallback: "${quoteSdn(fallback)}"
    selected_by: "${quoteSdn(selectedBy)}"
`);
  console.log(registryPath);
}

const supportedTuningMethods = [
  "retrieval-context-update",
  "prompt-tool-protocol-update",
  "provider-fine-tune",
  "local-lora",
  "local-qlora",
  "full-fine-tune",
  "new-model-architecture"
];

function commandFineTuneModelMethodOptions(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-model-method-options: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-model-method-options", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  console.log("model_candidates:");
  const block = registryBlockForAttempt(root, "model_research.sdn", attemptId);
  console.log(block || "  missing");
  console.log("supported_tuning_methods:");
  for (const method of supportedTuningMethods) {
    console.log(`  ${method}`);
  }
}

function commandFineTuneSelectModelMethod(args) {
  const [attemptId, baseModel, revision, deploymentTarget, method, selectedBy, fallback, reason = "selected during design"] = args;
  if (!attemptId || !baseModel || !revision || !deploymentTarget || !method || !selectedBy || !fallback) {
    console.error("spipe fine-tune-select-model-method: attempt_id, base_model, revision, deployment_target, method, selected_by, and fallback are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-select-model-method", attemptId)) return;
  if (!supportedTuningMethods.includes(method)) {
    console.error(`spipe fine-tune-select-model-method: invalid method: ${method}`);
    process.exitCode = 2;
    return;
  }
  commandFineTuneRecordModel([attemptId, baseModel, revision, reason, deploymentTarget]);
  commandFineTuneRecordMethod([attemptId, method, reason, fallback, selectedBy]);
}

function commandFineTuneRecordTraining(args) {
  const [attemptId, method, trainingScript, trainingCommand, modelArtifact] = args;
  if (!attemptId || !method || !trainingScript || !trainingCommand || !modelArtifact) {
    console.error("spipe fine-tune-record-training: attempt_id, method, training_script, training_command, and model_artifact are required");
    process.exitCode = 2;
    return;
  }
  if (!/^[A-Za-z0-9_.-]+$/.test(attemptId)) {
    console.error("spipe fine-tune-record-training: attempt_id may contain only letters, numbers, dot, dash, and underscore");
    process.exitCode = 2;
    return;
  }
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "training_scripts.sdn", "# Training script evidence for SPipe LLM fine-tune attempts.", "training_scripts");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    method: "${quoteSdn(method)}"
    training_script: "${quoteSdn(trainingScript)}"
    training_command: "${quoteSdn(trainingCommand)}"
    model_artifact: "${quoteSdn(modelArtifact)}"
`);
  console.log(registryPath);
}

function trainingScriptBody(attemptId, method, modelArtifact) {
  return `#!/bin/sh
set -eu

ATTEMPT_ID=${quoteShell(attemptId)}
METHOD=${quoteShell(method)}
MODEL_ARTIFACT=${quoteShell(modelArtifact)}

cat <<'MSG'
SPipe training scaffold.
Replace this script with the selected trainer/provider command after requirements,
model, method, data, and evaluation targets are finalized.
MSG

printf 'attempt_id=%s\\n' "$ATTEMPT_ID"
printf 'method=%s\\n' "$METHOD"
printf 'model_artifact=%s\\n' "$MODEL_ARTIFACT"
`;
}

function commandFineTuneScaffoldTraining(args) {
  const [attemptId, method, scriptPath, modelArtifact = "not-created"] = args;
  if (!attemptId || !method || !scriptPath) {
    console.error("spipe fine-tune-scaffold-training: attempt_id, method, and script_path are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-scaffold-training", attemptId)) return;
  if (!supportedTuningMethods.includes(method) && method !== "dry-run-record-only") {
    console.error(`spipe fine-tune-scaffold-training: invalid method: ${method}`);
    process.exitCode = 2;
    return;
  }
  const outPath = resolve(process.cwd(), scriptPath);
  mkdirSync(dirname(outPath), { recursive: true });
  writeFileSync(outPath, trainingScriptBody(attemptId, method, modelArtifact));
  chmodSync(outPath, 0o755);
  commandFineTuneRecordTraining([attemptId, method, scriptPath, `${scriptPath}`, modelArtifact]);
}

const retryStatuses = new Set([
  "retry-implementation",
  "retry-data-research",
  "retry-base-model",
  "retry-tuning-method",
  "try-other-way"
]);

function validateAttemptId(commandName, attemptId) {
  if (!/^[A-Za-z0-9_.-]+$/.test(attemptId)) {
    console.error(`spipe ${commandName}: attempt_id may contain only letters, numbers, dot, dash, and underscore`);
    process.exitCode = 2;
    return false;
  }
  return true;
}

function commandFineTuneRecordEval(args) {
  const [attemptId, evalCommand, metrics, target, result] = args;
  if (!attemptId || !evalCommand || !metrics || !target || !result) {
    console.error("spipe fine-tune-record-eval: attempt_id, eval_command, metrics, target, and result are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-eval", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "eval_results.sdn", "# Evaluation evidence for SPipe LLM fine-tune attempts.", "eval_results");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    eval_command: "${quoteSdn(evalCommand)}"
    metrics: "${quoteSdn(metrics)}"
    target: "${quoteSdn(target)}"
    result: "${quoteSdn(result)}"
`);
  console.log(registryPath);
}

function commandFineTuneRecordDecision(args) {
  const [attemptId, status, retryTarget, nextAttempt = "", notes = ""] = args;
  if (!attemptId || !status) {
    console.error("spipe fine-tune-record-decision: attempt_id and status are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-decision", attemptId)) return;
  if (status !== "accepted" && !retryStatuses.has(status)) {
    console.error(`spipe fine-tune-record-decision: invalid status: ${status}`);
    process.exitCode = 2;
    return;
  }
  if (retryStatuses.has(status) && !retryTarget) {
    console.error("spipe fine-tune-record-decision: retry_target is required for retry status");
    process.exitCode = 2;
    return;
  }
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "decisions.sdn", "# Verification decision evidence for SPipe LLM fine-tune attempts.", "decisions");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    status: "${quoteSdn(status)}"
    retry_target: "${quoteSdn(retryTarget || "")}"
    next_attempt: "${quoteSdn(nextAttempt)}"
    notes: "${quoteSdn(notes)}"
`);
  console.log(registryPath);
}

function commandFineTuneRecordVerifyLoop(args) {
  const [attemptId, evalCommand, metrics, target, result, status, retryTarget = "", nextAttempt = "", notes = ""] = args;
  if (!attemptId || !evalCommand || !metrics || !target || !result || !status) {
    console.error("spipe fine-tune-record-verify-loop: attempt_id, eval_command, metrics, target, result, and status are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-verify-loop", attemptId)) return;
  commandFineTuneRecordEval([attemptId, evalCommand, metrics, target, result]);
  if (process.exitCode) return;
  commandFineTuneRecordDecision([attemptId, status, retryTarget, nextAttempt, notes]);
  if (process.exitCode) return;
  if (status !== "accepted" && nextAttempt) {
    commandFineTuneCreateRetry([attemptId, nextAttempt, `Retry ${attemptId} via ${retryTarget}`, ""]);
  }
}

function commandFineTuneRecordProcess(args) {
  const [attemptId, researchDoc, requirementsDoc, nfrDoc, planDoc, architectureDoc, designDoc] = args;
  if (!attemptId || !researchDoc || !requirementsDoc || !nfrDoc || !planDoc || !architectureDoc || !designDoc) {
    console.error("spipe fine-tune-record-process: attempt_id, research_doc, requirements_doc, nfr_doc, plan_doc, architecture_doc, and design_doc are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-process", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "process_docs.sdn", "# Pipeline document trace for SPipe LLM fine-tune attempts.", "process_docs");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    research_doc: "${quoteSdn(researchDoc)}"
    requirements_doc: "${quoteSdn(requirementsDoc)}"
    nfr_doc: "${quoteSdn(nfrDoc)}"
    plan_doc: "${quoteSdn(planDoc)}"
    architecture_doc: "${quoteSdn(architectureDoc)}"
    design_doc: "${quoteSdn(designDoc)}"
`);
  console.log(registryPath);
}

function writeIfMissingWithDirs(path, content) {
  mkdirSync(dirname(path), { recursive: true });
  if (!existsSync(path)) {
    writeFileSync(path, content);
  }
}

function commandFineTuneScaffoldProcessDocs(args) {
  const [attemptId, featureSlug, title = featureSlug] = args;
  if (!attemptId || !featureSlug) {
    console.error("spipe fine-tune-scaffold-process-docs: attempt_id and feature_slug are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-scaffold-process-docs", attemptId)) return;
  if (!/^[A-Za-z0-9_.-]+$/.test(featureSlug)) {
    console.error("spipe fine-tune-scaffold-process-docs: feature_slug may contain only letters, numbers, dot, dash, and underscore");
    process.exitCode = 2;
    return;
  }

  const docs = {
    research: `doc/01_research/local/${featureSlug}.md`,
    requirements: `doc/02_requirements/feature/${featureSlug}_options.md`,
    nfr: `doc/02_requirements/nfr/${featureSlug}_options.md`,
    plan: `doc/03_plan/agent_tasks/${featureSlug}.md`,
    architecture: `doc/04_architecture/${featureSlug}.md`,
    design: `doc/05_design/${featureSlug}.md`
  };

  writeIfMissingWithDirs(join(process.cwd(), docs.research), `# ${title} Local Research

Attempt: ${attemptId}

## Local Findings

- Source paths:
- Existing process/docs:
- Data sources:
`);
  writeIfMissingWithDirs(join(process.cwd(), docs.requirements), `# ${title} Requirement Options

Attempt: ${attemptId}

## Option A: Scaffold

Requirements:
- Record the selected user-facing behavior.

Pros:
- Fast to validate.

Cons:
- Needs expansion before implementation.

Effort: Medium.
`);
  writeIfMissingWithDirs(join(process.cwd(), docs.nfr), `# ${title} NFR Options

Attempt: ${attemptId}

## Option A: Auditability First

Targets:
- Record evidence for each process phase.

Pros: Clear release evidence.
Cons: More records to maintain.
Effort: Medium.
`);
  writeIfMissingWithDirs(join(process.cwd(), docs.plan), `# ${title} Agent Task Plan

Attempt: ${attemptId}

1. Complete research and data download evidence.
2. Select requirements and NFRs.
3. Choose base model and tuning method.
4. Implement/train and record artifacts.
5. Verify and route retry.
`);
  writeIfMissingWithDirs(join(process.cwd(), docs.architecture), `# ${title} Architecture

Attempt: ${attemptId}

## Layers

- Host records:
- SPipe reusable process:
- Trainer/provider adapter:
- App/server handoff:
`);
  writeIfMissingWithDirs(join(process.cwd(), docs.design), `# ${title} Design

Attempt: ${attemptId}

## Design Decisions

- Data:
- Base model:
- Tuning method:
- Evaluation:
- Retry route:
`);
  commandFineTuneRecordProcess([attemptId, docs.research, docs.requirements, docs.nfr, docs.plan, docs.architecture, docs.design]);
}

function commandFineTuneRecordRequirements(args) {
  const [attemptId, featureOption, nfrOption, selectedBy, selectionDoc, notes = ""] = args;
  if (!attemptId || !featureOption || !nfrOption || !selectedBy || !selectionDoc) {
    console.error("spipe fine-tune-record-requirements: attempt_id, feature_option, nfr_option, selected_by, and selection_doc are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-requirements", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "requirements_selection.sdn", "# Requirement option selection evidence for SPipe LLM fine-tune attempts.", "requirements_selection");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    feature_option: "${quoteSdn(featureOption)}"
    nfr_option: "${quoteSdn(nfrOption)}"
    selected_by: "${quoteSdn(selectedBy)}"
    selection_doc: "${quoteSdn(selectionDoc)}"
    notes: "${quoteSdn(notes)}"
`);
  console.log(registryPath);
}

const featureOptionsRel = "doc/02_requirements/feature/spipe_llm_finetune_process_options.md";
const nfrOptionsRel = "doc/02_requirements/nfr/spipe_llm_finetune_process_options.md";
const featureRequirementsRel = "doc/02_requirements/feature/spipe_llm_finetune_process.md";
const nfrRequirementsRel = "doc/02_requirements/nfr/spipe_llm_finetune_process.md";

function normalizeOption(value) {
  const match = String(value || "").trim().match(/(?:option[-_\s]*)?([A-Za-z])$/i);
  return match ? match[1].toUpperCase() : "";
}

function normalizeOptionList(value) {
  const raw = String(value || "").trim();
  if (!raw) return [];
  const matches = [...raw.matchAll(/[A-Za-z]/g)].map((match) => match[0].toUpperCase());
  return [...new Set(matches)];
}

function optionHeadings(path) {
  if (!existsSync(path)) return [];
  const content = readFileSync(path, "utf8");
  return [...content.matchAll(/^## Option ([A-Z]):\s*(.+)$/gm)].map((match) => ({
    letter: match[1],
    title: match[2].trim()
  }));
}

function selectedOptionBlock(path, option) {
  if (!existsSync(path)) return null;
  const content = readFileSync(path, "utf8");
  const letter = normalizeOption(option);
  const header = new RegExp(`^## Option ${letter}:\\s*(.+)$`, "m");
  const match = content.match(header);
  if (!match || match.index === undefined) return null;
  const rest = content.slice(match.index);
  const next = rest.slice(match[0].length).search(/\n## (Option [A-Z]:|Selection Needed)/);
  const block = next === -1 ? rest : rest.slice(0, match[0].length + next);
  return {
    letter,
    title: match[1].trim(),
    block: block.trimEnd()
  };
}

function selectedOptionBlocks(path, options) {
  const letters = normalizeOptionList(options);
  return letters.map((letter) => selectedOptionBlock(path, letter));
}

function commandFineTuneOptions() {
  const hostRoot = process.cwd();
  const featurePath = join(hostRoot, featureOptionsRel);
  const nfrPath = join(hostRoot, nfrOptionsRel);
  console.log("feature_options:");
  for (const option of optionHeadings(featurePath)) {
    console.log(`  ${option.letter}: ${option.title}`);
  }
  console.log("nfr_options:");
  for (const option of optionHeadings(nfrPath)) {
    console.log(`  ${option.letter}: ${option.title}`);
  }
}

function writeSelectedDoc(path, title, sourceRel, selectedItems, selectedBy, notes) {
  mkdirSync(dirname(path), { recursive: true });
  const selected = Array.isArray(selectedItems) ? selectedItems : [selectedItems];
  const selectedLine = selected.map((item) => `Option ${item.letter}: ${item.title}`).join(" -> ");
  const body = selected.map((item) => item.block).join("\n\n");
  writeFileSync(path, `# ${title}

Selected option: ${selectedLine}
Selected by: ${selectedBy}
Source options: ${sourceRel}
Notes: ${notes || ""}

${body}
`);
}

function commandFineTuneSelectRequirements(args) {
  const [attemptId, featureOptionArg, nfrOptionArg, selectedBy, notes = ""] = args;
  if (!attemptId || !featureOptionArg || !nfrOptionArg || !selectedBy) {
    console.error("spipe fine-tune-select-requirements: attempt_id, feature_option, nfr_option, and selected_by are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-select-requirements", attemptId)) return;

  const hostRoot = process.cwd();
  const featureOptionsPath = join(hostRoot, featureOptionsRel);
  const nfrOptionsPath = join(hostRoot, nfrOptionsRel);
  const featureSelected = selectedOptionBlocks(featureOptionsPath, featureOptionArg);
  const nfrSelected = selectedOptionBlocks(nfrOptionsPath, nfrOptionArg);
  if (!featureSelected.length || featureSelected.some((item) => !item)) {
    console.error(`spipe fine-tune-select-requirements: feature option not found: ${featureOptionArg}`);
    process.exitCode = 1;
    return;
  }
  if (!nfrSelected.length || nfrSelected.some((item) => !item)) {
    console.error(`spipe fine-tune-select-requirements: nfr option not found: ${nfrOptionArg}`);
    process.exitCode = 1;
    return;
  }

  writeSelectedDoc(join(hostRoot, featureRequirementsRel), "SPipe LLM Fine-Tune Process Requirements", featureOptionsRel, featureSelected, selectedBy, notes);
  writeSelectedDoc(join(hostRoot, nfrRequirementsRel), "SPipe LLM Fine-Tune Process NFR Requirements", nfrOptionsRel, nfrSelected, selectedBy, notes);
  rmSync(featureOptionsPath, { force: true });
  rmSync(nfrOptionsPath, { force: true });
  commandFineTuneRecordRequirements([
    attemptId,
    featureSelected.map((item) => `Option ${item.letter}`).join(" -> "),
    nfrSelected.map((item) => `Option ${item.letter}`).join(" + "),
    selectedBy,
    featureRequirementsRel,
    notes
  ]);
  console.log(featureRequirementsRel);
  console.log(nfrRequirementsRel);
}

function commandFineTuneRecordApp(args) {
  const [attemptId, appTarget, usage, handoffDoc] = args;
  if (!attemptId || !appTarget || !usage || !handoffDoc) {
    console.error("spipe fine-tune-record-app: attempt_id, app_target, usage, and handoff_doc are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-app", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "app_handoffs.sdn", "# LLM-backed app/server handoff evidence for SPipe fine-tune attempts.", "app_handoffs");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    app_target: "${quoteSdn(appTarget)}"
    usage: "${quoteSdn(usage)}"
    handoff_doc: "${quoteSdn(handoffDoc)}"
`);
  console.log(registryPath);
}

function commandFineTuneRecordRetune(args) {
  const [attemptId, reason, sourceEval, nextAttempt, retryTarget] = args;
  if (!attemptId || !reason || !sourceEval || !nextAttempt || !retryTarget) {
    console.error("spipe fine-tune-record-retune: attempt_id, reason, source_eval, next_attempt, and retry_target are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-record-retune", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const registryPath = initRegistry(root, "retune_requests.sdn", "# Retune request evidence for SPipe LLM-backed app/server loops.", "retune_requests");
  appendFileSync(registryPath, `  - attempt_id: "${quoteSdn(attemptId)}"
    reason: "${quoteSdn(reason)}"
    source_eval: "${quoteSdn(sourceEval)}"
    next_attempt: "${quoteSdn(nextAttempt)}"
    retry_target: "${quoteSdn(retryTarget)}"
`);
  console.log(registryPath);
}

function commandFineTuneCreateRetry(args) {
  const [sourceAttemptId, nextAttemptId, goal = "", target = ""] = args;
  if (!sourceAttemptId || !nextAttemptId) {
    console.error("spipe fine-tune-create-retry: source_attempt_id and next_attempt_id are required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-create-retry", sourceAttemptId)) return;
  if (!validateAttemptId("fine-tune-create-retry", nextAttemptId)) return;

  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const sourceAttemptPath = join(root, "attempts", `${sourceAttemptId}.sdn`);
  const sourceContent = existsSync(sourceAttemptPath) ? readFileSync(sourceAttemptPath, "utf8") : "";
  const status = registryValueForAttempt(root, "decisions.sdn", sourceAttemptId, "status") || readQuotedValue(sourceContent, "status");
  const retryTarget = registryValueForAttempt(root, "decisions.sdn", sourceAttemptId, "retry_target") || readQuotedValue(sourceContent, "retry_target");

  if (!status || status === "accepted") {
    console.error(`spipe fine-tune-create-retry: source attempt has no retry decision: ${sourceAttemptId}`);
    process.exitCode = 1;
    return;
  }
  if (!retryTarget) {
    console.error(`spipe fine-tune-create-retry: source attempt has no retry target: ${sourceAttemptId}`);
    process.exitCode = 1;
    return;
  }

  const nextGoal = goal || `Retry ${sourceAttemptId} via ${retryTarget}`;
  commandFineTuneNewAttempt([nextAttemptId, nextGoal, target]);
  if (process.exitCode) return;
  commandFineTuneRecordRetune([sourceAttemptId, status, `decisions.sdn:${sourceAttemptId}`, nextAttemptId, retryTarget]);
}

function commandFineTuneAppHandoff(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-app-handoff: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-app-handoff", attemptId)) return;
  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  console.log("# SPipe LLM App/Server Handoff");
  console.log(`attempt_id: ${attemptId}`);
  console.log("");
  console.log("## App Handoff");
  console.log(registryBlockForAttempt(root, "app_handoffs.sdn", attemptId) || "missing");
  console.log("");
  console.log("## Model");
  console.log(registryBlockForAttempt(root, "models.sdn", attemptId) || "missing");
  console.log("");
  console.log("## Training");
  console.log(registryBlockForAttempt(root, "training_scripts.sdn", attemptId) || "missing");
  console.log("");
  console.log("## Evaluation");
  console.log(registryBlockForAttempt(root, "eval_results.sdn", attemptId) || "missing");
  console.log("");
  console.log("## Decision");
  console.log(registryBlockForAttempt(root, "decisions.sdn", attemptId) || "missing");
  console.log("");
  console.log("## Retune Requests");
  console.log(registryBlockForAttempt(root, "retune_requests.sdn", attemptId) || "missing");
}

function registryHasAttempt(root, fileName, attemptId) {
  const path = join(root, fileName);
  if (!existsSync(path)) return false;
  const content = readFileSync(path, "utf8");
  return content.includes(`attempt_id: "${attemptId}"`);
}

function commandFineTuneStatus(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-status: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-status", attemptId)) return;

  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const attemptPath = join(root, "attempts", `${attemptId}.sdn`);
  const checks = [
    ["attempt_record", existsSync(attemptPath)],
    ["data_downloads", registryHasAttempt(root, "data_downloads.sdn", attemptId)],
    ["data_checks", registryHasAttempt(root, "data_checks.sdn", attemptId)],
    ["process_docs", registryHasAttempt(root, "process_docs.sdn", attemptId)],
    ["requirements_selection", registryHasAttempt(root, "requirements_selection.sdn", attemptId)],
    ["model_research", registryHasAttempt(root, "model_research.sdn", attemptId)],
    ["model_architecture", registryHasAttempt(root, "model_architecture.sdn", attemptId)],
    ["tuning_methods", registryHasAttempt(root, "tuning_methods.sdn", attemptId)],
    ["models", registryHasAttempt(root, "models.sdn", attemptId)],
    ["training_scripts", registryHasAttempt(root, "training_scripts.sdn", attemptId)],
    ["eval_results", registryHasAttempt(root, "eval_results.sdn", attemptId)],
    ["decisions", registryHasAttempt(root, "decisions.sdn", attemptId)],
    ["app_handoffs", registryHasAttempt(root, "app_handoffs.sdn", attemptId)],
    ["retune_requests", registryHasAttempt(root, "retune_requests.sdn", attemptId)]
  ];

  let failures = 0;
  console.log(`attempt_id=${attemptId}`);
  for (const [name, ok] of checks) {
    if (!ok) failures += 1;
    console.log(`${name}=${ok ? "present" : "missing"}`);
  }
  console.log(failures === 0 ? "STATUS: PASS llm-finetune-status" : "STATUS: FAIL llm-finetune-status");
  process.exitCode = failures === 0 ? 0 : 1;
}

function hasPlaceholder(value) {
  return !value
    || value.includes("pending")
    || value === "not-selected"
    || value === "not-created"
    || value === "dry-run-record-only";
}

function commandFineTuneDoctor(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-doctor: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-doctor", attemptId)) return;

  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const attemptPath = join(root, "attempts", `${attemptId}.sdn`);
  const attemptContent = existsSync(attemptPath) ? readFileSync(attemptPath, "utf8") : "";
  const requiredRegistries = [
    "data_downloads.sdn",
    "data_checks.sdn",
    "process_docs.sdn",
    "requirements_selection.sdn",
    "model_research.sdn",
    "model_architecture.sdn",
    "tuning_methods.sdn",
    "models.sdn",
    "training_scripts.sdn",
    "eval_results.sdn",
    "decisions.sdn",
    "app_handoffs.sdn",
    "retune_requests.sdn"
  ];

  let failures = 0;
  let warnings = 0;
  console.log(`attempt_id=${attemptId}`);
  if (!existsSync(attemptPath)) {
    failures += 1;
    console.log("ERROR missing_attempt_record");
  }

  for (const fileName of requiredRegistries) {
    if (!registryHasAttempt(root, fileName, attemptId)) {
      warnings += 1;
      console.log(`WARN missing_registry_evidence ${fileName}`);
    }
  }

  const fields = [
    ["feature_option", registryValueForAttempt(root, "requirements_selection.sdn", attemptId, "feature_option")],
    ["nfr_option", registryValueForAttempt(root, "requirements_selection.sdn", attemptId, "nfr_option")],
    ["base_model", registryValueForAttempt(root, "models.sdn", attemptId, "base_model") || readQuotedValue(attemptContent, "base_model")],
    ["tuning_method", registryValueForAttempt(root, "tuning_methods.sdn", attemptId, "method") || readQuotedValue(attemptContent, "method")],
    ["model_artifact", registryValueForAttempt(root, "training_scripts.sdn", attemptId, "model_artifact") || readQuotedValue(attemptContent, "model_artifact")],
    ["decision_status", registryValueForAttempt(root, "decisions.sdn", attemptId, "status") || readQuotedValue(attemptContent, "status")]
  ];
  for (const [name, value] of fields) {
    if (hasPlaceholder(value)) {
      warnings += 1;
      console.log(`WARN placeholder ${name}=${value || "(missing)"}`);
    }
  }

  const next = readinessChecks(root, attemptId).find(([, ok]) => !ok);
  console.log(`next_action=${next ? next[0] : "ready"}`);
  const ready = !next && failures === 0;
  console.log(ready ? "STATUS: PASS llm-finetune-doctor" : failures ? "STATUS: FAIL llm-finetune-doctor" : "STATUS: WARN llm-finetune-doctor");
  process.exitCode = ready ? 0 : failures ? 1 : 1;
}

function registryValueForAttempt(root, fileName, attemptId, key) {
  const path = join(root, fileName);
  if (!existsSync(path)) return "";
  const lines = readFileSync(path, "utf8").split(/\r?\n/);
  let inAttempt = false;
  let latest = "";
  for (const line of lines) {
    const attemptMatch = line.match(/^\s*-\s*attempt_id:\s*"([^"]*)"\s*$/);
    if (attemptMatch) {
      inAttempt = attemptMatch[1] === attemptId;
      continue;
    }
    if (inAttempt) {
      const valueMatch = line.match(new RegExp(`^\\s*${key}:\\s*"([^"]*)"\\s*$`));
      if (valueMatch) latest = valueMatch[1];
    }
  }
  return latest;
}

function commandFineTuneReady(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-ready: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-ready", attemptId)) return;

  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const attemptPath = join(root, "attempts", `${attemptId}.sdn`);
  let failures = 0;
  if (!existsSync(attemptPath)) {
    console.log(`ERROR missing_attempt_record ${attemptId}`);
    failures += 1;
  }

  const attemptContent = existsSync(attemptPath) ? readFileSync(attemptPath, "utf8") : "";
  const featureOption = registryValueForAttempt(root, "requirements_selection.sdn", attemptId, "feature_option");
  const nfrOption = registryValueForAttempt(root, "requirements_selection.sdn", attemptId, "nfr_option");
  const baseModel = registryValueForAttempt(root, "models.sdn", attemptId, "base_model") || readQuotedValue(attemptContent, "base_model");
  const method = registryValueForAttempt(root, "tuning_methods.sdn", attemptId, "method") || readQuotedValue(attemptContent, "method");
  const modelArtifact = registryValueForAttempt(root, "training_scripts.sdn", attemptId, "model_artifact") || readQuotedValue(attemptContent, "model_artifact");
  const status = registryValueForAttempt(root, "decisions.sdn", attemptId, "status") || readQuotedValue(attemptContent, "status");

  const checks = [
    ["feature_option_selected", featureOption && featureOption !== "pending-user-selection"],
    ["nfr_option_selected", nfrOption && nfrOption !== "pending-user-selection"],
    ["base_model_selected", baseModel && baseModel !== "not-selected"],
    ["tuning_method_real", method && method !== "dry-run-record-only"],
    ["model_artifact_created", modelArtifact && modelArtifact !== "not-created"],
    ["decision_accepted", status === "accepted"]
  ];

  console.log(`attempt_id=${attemptId}`);
  for (const [name, ok] of checks) {
    if (!ok) failures += 1;
    console.log(`${name}=${ok ? "ready" : "pending"}`);
  }
  console.log(failures === 0 ? "STATUS: PASS llm-finetune-ready" : "STATUS: FAIL llm-finetune-ready");
  process.exitCode = failures === 0 ? 0 : 1;
}

function readinessChecks(root, attemptId) {
  const attemptPath = join(root, "attempts", `${attemptId}.sdn`);
  const attemptContent = existsSync(attemptPath) ? readFileSync(attemptPath, "utf8") : "";
  const featureOption = registryValueForAttempt(root, "requirements_selection.sdn", attemptId, "feature_option");
  const nfrOption = registryValueForAttempt(root, "requirements_selection.sdn", attemptId, "nfr_option");
  const baseModel = registryValueForAttempt(root, "models.sdn", attemptId, "base_model") || readQuotedValue(attemptContent, "base_model");
  const method = registryValueForAttempt(root, "tuning_methods.sdn", attemptId, "method") || readQuotedValue(attemptContent, "method");
  const modelArtifact = registryValueForAttempt(root, "training_scripts.sdn", attemptId, "model_artifact") || readQuotedValue(attemptContent, "model_artifact");
  const status = registryValueForAttempt(root, "decisions.sdn", attemptId, "status") || readQuotedValue(attemptContent, "status");
  return [
    ["requirements-selection", featureOption && featureOption !== "pending-user-selection" && nfrOption && nfrOption !== "pending-user-selection"],
    ["base-model-selection", baseModel && baseModel !== "not-selected"],
    ["tuning-method-selection", method && method !== "dry-run-record-only"],
    ["model-artifact", modelArtifact && modelArtifact !== "not-created"],
    ["acceptance-decision", status === "accepted"]
  ];
}

function commandFineTuneNext(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-next: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-next", attemptId)) return;

  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const attemptPath = join(root, "attempts", `${attemptId}.sdn`);
  if (!existsSync(attemptPath)) {
    console.log(`attempt_id=${attemptId}`);
    console.log("next_action=create-attempt");
    process.exitCode = 1;
    return;
  }
  for (const [action, ok] of readinessChecks(root, attemptId)) {
    if (!ok) {
      console.log(`attempt_id=${attemptId}`);
      console.log(`next_action=${action}`);
      process.exitCode = 1;
      return;
    }
  }
  console.log(`attempt_id=${attemptId}`);
  console.log("next_action=ready");
}

function registryBlockForAttempt(root, fileName, attemptId) {
  const path = join(root, fileName);
  if (!existsSync(path)) return "";
  const lines = readFileSync(path, "utf8").split(/\r?\n/);
  let out = [];
  let latest = [];
  let inAttempt = false;
  for (const line of lines) {
    const attemptMatch = line.match(/^(\s*)-\s*attempt_id:\s*"([^"]*)"\s*$/);
    if (attemptMatch) {
      if (inAttempt) latest = out;
      inAttempt = attemptMatch[2] === attemptId;
      out = [];
      if (inAttempt) out.push(line);
      continue;
    }
    if (inAttempt) {
      out.push(line);
    }
  }
  if (inAttempt) latest = out;
  return latest.join("\n").trimEnd();
}

function commandFineTuneReport(args) {
  const [attemptId] = args;
  if (!attemptId) {
    console.error("spipe fine-tune-report: attempt_id is required");
    process.exitCode = 2;
    return;
  }
  if (!validateAttemptId("fine-tune-report", attemptId)) return;

  const root = join(process.cwd(), ".spipe/llm-finetune-process");
  const attemptPath = join(root, "attempts", `${attemptId}.sdn`);
  console.log(`# SPipe Fine-Tune Attempt Report`);
  console.log(`attempt_id: ${attemptId}`);
  console.log("");
  console.log("## Attempt Record");
  if (existsSync(attemptPath)) {
    process.stdout.write(readFileSync(attemptPath, "utf8").trimEnd());
    console.log("");
  } else {
    console.log("missing");
  }

  const registries = [
    ["Requirements Selection", "requirements_selection.sdn"],
    ["Process Docs", "process_docs.sdn"],
    ["Data Downloads", "data_downloads.sdn"],
    ["Data Checks", "data_checks.sdn"],
    ["Model Research", "model_research.sdn"],
    ["Model Architecture", "model_architecture.sdn"],
    ["Tuning Methods", "tuning_methods.sdn"],
    ["Models", "models.sdn"],
    ["Training Scripts", "training_scripts.sdn"],
    ["Eval Results", "eval_results.sdn"],
    ["Decisions", "decisions.sdn"],
    ["App Handoffs", "app_handoffs.sdn"],
    ["Retune Requests", "retune_requests.sdn"]
  ];

  for (const [title, fileName] of registries) {
    console.log("");
    console.log(`## ${title}`);
    const block = registryBlockForAttempt(root, fileName, attemptId);
    console.log(block || "missing");
  }
}

function commandFineTuneVerify(recordPath) {
  if (!recordPath) {
    console.error("spipe fine-tune-verify: record path is required");
    process.exitCode = 2;
    return;
  }
  if (!existsSync(recordPath)) {
    console.log(`ERROR missing_record ${recordPath}`);
    console.log("STATUS: FAIL llm-finetune-attempt-record");
    process.exitCode = 1;
    return;
  }

  const content = readFileSync(recordPath, "utf8");
  const required = [
    "attempt_id",
    "goal",
    "research_doc",
    "feature_option",
    "nfr_option",
    "selection_doc",
    "requirements_doc",
    "nfr_doc",
    "plan_doc",
    "architecture_doc",
    "design_doc",
    "candidate_model",
    "base_model",
    "base_model_reason",
    "download_command",
    "cache_path",
    "method",
    "training_script",
    "training_command",
    "model_artifact",
    "eval_command",
    "metrics",
    "target",
    "result",
    "status",
    "app_target",
    "handoff_doc"
  ];

  let failures = 0;
  for (const key of required) {
    if (!readQuotedValue(content, key)) {
      failures += 1;
      console.log(`ERROR missing_field ${key}`);
    }
  }

  const status = readQuotedValue(content, "status");
  const retryTarget = readQuotedValue(content, "retry_target");
  if (status && status !== "accepted" && !retryStatuses.has(status)) {
    failures += 1;
    console.log(`ERROR invalid_status ${status}`);
  }
  if (retryStatuses.has(status) && !retryTarget) {
    failures += 1;
    console.log("ERROR missing_field retry_target");
  }

  const trainingScript = readQuotedValue(content, "training_script");
  if (trainingScript && trainingScript !== "provider-managed") {
    const scriptPath = resolve(process.cwd(), trainingScript);
    if (!existsSync(scriptPath)) {
      failures += 1;
      console.log(`ERROR missing_training_script ${trainingScript}`);
    }
  }

  console.log(failures === 0 ? "STATUS: PASS llm-finetune-attempt-record" : "STATUS: FAIL llm-finetune-attempt-record");
  process.exitCode = failures === 0 ? 0 : 1;
}

const [command, ...args] = process.argv.slice(2);
const arg = args[0];
switch (command) {
  case undefined:
  case "--help":
  case "-h":
    printUsage();
    break;
  case "--version":
  case "-v":
    console.log("0.1.0");
    break;
  case "info":
    commandInfo();
    break;
  case "experts":
    commandExperts();
    break;
  case "link-plan":
    commandLinkPlan(arg);
    break;
  case "doc-root":
    commandDocRoot(arg);
    break;
  case "doc-link":
    commandDocLink(arg, args[1]);
    break;
  case "doctor":
    commandDoctor(arg);
    break;
  case "skill":
    commandSkill();
    break;
  case "fine-tune-guide":
    commandFineTuneGuide();
    break;
  case "fine-tune-model-guide":
    commandFineTuneModelGuide();
    break;
  case "fine-tune-template":
    commandFineTuneTemplate();
    break;
  case "fine-tune-init":
    commandFineTuneInit();
    break;
  case "fine-tune-new-attempt":
    commandFineTuneNewAttempt(args);
    break;
  case "fine-tune-record-data":
    commandFineTuneRecordData(args);
    break;
  case "fine-tune-data-plan":
    commandFineTuneDataPlan(args);
    break;
  case "fine-tune-record-data-check":
    commandFineTuneRecordDataCheck(args);
    break;
  case "fine-tune-record-model":
    commandFineTuneRecordModel(args);
    break;
  case "fine-tune-record-model-research":
    commandFineTuneRecordModelResearch(args);
    break;
  case "fine-tune-record-model-arch":
    commandFineTuneRecordModelArch(args);
    break;
  case "fine-tune-scaffold-model-arch":
    commandFineTuneScaffoldModelArch(args);
    break;
  case "fine-tune-record-method":
    commandFineTuneRecordMethod(args);
    break;
  case "fine-tune-model-method-options":
    commandFineTuneModelMethodOptions(args);
    break;
  case "fine-tune-select-model-method":
    commandFineTuneSelectModelMethod(args);
    break;
  case "fine-tune-record-training":
    commandFineTuneRecordTraining(args);
    break;
  case "fine-tune-scaffold-training":
    commandFineTuneScaffoldTraining(args);
    break;
  case "fine-tune-record-eval":
    commandFineTuneRecordEval(args);
    break;
  case "fine-tune-record-decision":
    commandFineTuneRecordDecision(args);
    break;
  case "fine-tune-record-verify-loop":
    commandFineTuneRecordVerifyLoop(args);
    break;
  case "fine-tune-record-process":
    commandFineTuneRecordProcess(args);
    break;
  case "fine-tune-scaffold-process-docs":
    commandFineTuneScaffoldProcessDocs(args);
    break;
  case "fine-tune-record-requirements":
    commandFineTuneRecordRequirements(args);
    break;
  case "fine-tune-options":
    commandFineTuneOptions();
    break;
  case "fine-tune-select-requirements":
    commandFineTuneSelectRequirements(args);
    break;
  case "fine-tune-record-app":
    commandFineTuneRecordApp(args);
    break;
  case "fine-tune-record-retune":
    commandFineTuneRecordRetune(args);
    break;
  case "fine-tune-create-retry":
    commandFineTuneCreateRetry(args);
    break;
  case "fine-tune-app-handoff":
    commandFineTuneAppHandoff(args);
    break;
  case "fine-tune-status":
    commandFineTuneStatus(args);
    break;
  case "fine-tune-doctor":
    commandFineTuneDoctor(args);
    break;
  case "fine-tune-ready":
    commandFineTuneReady(args);
    break;
  case "fine-tune-next":
    commandFineTuneNext(args);
    break;
  case "fine-tune-report":
    commandFineTuneReport(args);
    break;
  case "fine-tune-verify":
    commandFineTuneVerify(arg);
    break;
  default:
    console.error(`spipe: unknown command: ${command}`);
    printUsage();
    process.exitCode = 2;
}
