import { initializeResult } from "./initialize.js";
import { readResource, resources } from "./resources.js";
import { createToolCaller, tools } from "./tools.js";

function result(id, value) {
  return { jsonrpc: "2.0", id, result: value };
}

export function createRouter({ moduleRoot, reverseReferenceService, serverVersion } = {}) {
  const callTool = createToolCaller(moduleRoot, { reverseReferenceService });
  return function route(message) {
    if (message.method === "initialize") return result(message.id, initializeResult(serverVersion));
    if (message.method === "tools/list") return result(message.id, { tools });
    if (message.method === "tools/call") {
      const params = message.params || {};
      return result(message.id, callTool(params.name, params.arguments || {}));
    }
    if (message.method === "resources/list") return result(message.id, { resources });
    if (message.method === "resources/read") return result(message.id, readResource(moduleRoot, message.params?.uri));
    if (message.id === undefined) return undefined;
    return result(message.id, {});
  };
}
