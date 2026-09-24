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
      // A JSON parse failure has no `message` to read an id from, so those
      // stay id:null. But a handler/router throw AFTER a successful parse
      // (e.g. an unknown tool, a missing param) has a real request id — echo
      // it back instead of dropping it, so callers can still correlate the
      // error response with their request.
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
