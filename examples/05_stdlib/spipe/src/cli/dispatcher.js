import { printUsage } from "./usage.js";

export async function runCli(argv = process.argv.slice(2)) {
  const [command, ...args] = argv;
  if (command === undefined || command === "--help" || command === "-h") {
    printUsage();
    return;
  }
  if (command === "--version" || command === "-v") {
    console.log("0.2.0");
    return;
  }
  if (command === "release-guide") {
    const { readFileSync } = await import("node:fs");
    const { fileURLToPath } = await import("node:url");
    const { dirname, join } = await import("node:path");
    const here = dirname(fileURLToPath(import.meta.url));
    console.log(readFileSync(join(here, "../../doc/00_llm_process/skill_command/command/release.md"), "utf8"));
    return;
  }
  if (command === "release-capabilities") {
    console.log("schema.vcs_policy=spipe-vcs/3");
    console.log("schema.session=spipe-session/1");
    console.log("schema.release=spipe-release/1");
    console.log("schema.candidate=spipe-candidate/1");
    console.log("capability.isolated_sessions=true");
    console.log("capability.reviewed_beta_backports=true");
    console.log("capability.promote_without_rebuild=true");
    return;
  }
  const { runHostCommand } = await import("./host_commands.js");
  const hostResult = runHostCommand(command, args);
  if (hostResult.handled) return hostResult;
  const { runFineTuneCommand } = await import("./fine_tune_commands.js");
  const fineTuneResult = runFineTuneCommand(command, args);
  if (fineTuneResult.handled) return fineTuneResult;

  console.error(`spipe: unknown command: ${command}`);
  printUsage();
  process.exitCode = 2;
  return fineTuneResult;
}
