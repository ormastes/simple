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
      // JSON-RPC clients match responses by request id; a null id makes error
      // replies unmatchable and looks like a hung call. Preserve the id of the
      // offending message when one was parsed (parse failures keep a null id,
      // matching JSON-RPC 2.0 for errors without an id).
      const id = message !== null && typeof message === "object" && "id" in message ? message.id : null;
      write(`${stableJson(errorResult(id, error))}\n`);
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
