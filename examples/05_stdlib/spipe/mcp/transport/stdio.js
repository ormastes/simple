import { errorResult } from "../protocol/errors.js";
import { stableJson } from "../../src/format/stable.js";

export function createLineHandler(router, write) {
  return function handleLine(line) {
    let message;
    try {
      message = JSON.parse(line);
      const response = router(message);
      if (response !== undefined) write(`${stableJson(response)}\n`);
    } catch (error) {
      // A JSON.parse failure has no id to recover (message stays undefined) —
      // that case is still reported with a null id, per JSON-RPC 2.0 §5.
      // A handler failure (thrown deep in the router, e.g. tools.js's
      // allowlist check) DOES have a valid parsed message with its own id;
      // discarding it here broke request/response correlation for every
      // tool call that throws, which is most of the validated spipe_release_*
      // tools. Preserve it when available.
      write(`${stableJson(errorResult(message?.id ?? null, error))}\n`);
    }
  };
}

export function runStdioTransport(router, input = process.stdin, output = process.stdout) {
  let buffer = "";
  const handleLine = createLineHandler(router, (content) => output.write(content));
  input.setEncoding("utf8");
  input.on("data", (chunk) => {
    buffer += chunk;
    let newline;
    while ((newline = buffer.indexOf("\n")) >= 0) {
      const line = buffer.slice(0, newline).trim();
      buffer = buffer.slice(newline + 1);
      if (line) handleLine(line);
    }
  });
}
