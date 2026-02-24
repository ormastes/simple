import { spawn } from "node:child_process";

type Json = Record<string, any>;

function sendMsg(stdin: NodeJS.WritableStream, obj: Json): void {
  const body = Buffer.from(JSON.stringify(obj), "utf8");
  const header = Buffer.from(`Content-Length: ${body.length}\r\n\r\n`, "ascii");
  stdin.write(header);
  stdin.write(body);
}

function createReader(stdout: NodeJS.ReadableStream): () => Promise<Json> {
  let buf = Buffer.alloc(0);
  const queue: Json[] = [];
  let resolve: ((value: Json) => void) | null = null;
  let reject: ((err: any) => void) | null = null;

  function tryParse(): void {
    while (true) {
      const marker = buf.indexOf("\r\n\r\n");
      if (marker < 0) return;
      const header = buf.subarray(0, marker).toString("utf8");
      const m = header.match(/Content-Length:\s*(\d+)/i);
      if (!m) {
        if (reject) reject(new Error("Missing Content-Length"));
        return;
      }
      const len = Number(m[1]);
      const start = marker + 4;
      if (buf.length < start + len) return;
      const body = buf.subarray(start, start + len).toString("utf8");
      buf = buf.subarray(start + len);
      const msg = JSON.parse(body) as Json;
      if (resolve) {
        const r = resolve;
        resolve = null;
        reject = null;
        r(msg);
      } else {
        queue.push(msg);
      }
    }
  }

  stdout.on("data", (chunk) => {
    buf = Buffer.concat([buf, chunk as Buffer]);
    tryParse();
  });
  stdout.on("error", (err) => {
    if (reject) reject(err);
  });

  return async function readMsg(): Promise<Json> {
    if (queue.length > 0) return queue.shift()!;
    return new Promise<Json>((res, rej) => {
      resolve = res;
      reject = rej;
    });
  };
}

function assertOk(cond: boolean, msg: string): void {
  if (!cond) throw new Error(msg);
}

async function main(): Promise<number> {
  const proc = spawn("bin/simple_mcp_server", [], { stdio: ["pipe", "pipe", "ignore"] });
  const readMsg = createReader(proc.stdout);

  sendMsg(proc.stdin, {
    jsonrpc: "2.0",
    id: "1",
    method: "initialize",
    params: {
      protocolVersion: "2025-06-18",
      capabilities: {},
      clientInfo: { name: "probe-typescript", version: "1.0" },
    },
  });
  const initResp = await readMsg();
  assertOk(!!initResp.result, "initialize failed");

  sendMsg(proc.stdin, { jsonrpc: "2.0", method: "initialized", params: {} });

  sendMsg(proc.stdin, { jsonrpc: "2.0", id: "2", method: "tools/list", params: {} });
  const toolsResp = await readMsg();
  const names = new Set<string>((toolsResp.result?.tools ?? []).map((t: any) => t.name));
  assertOk(names.has("debug_create_session"), "debug_create_session missing from tools/list");
  assertOk(names.has("debug_log_status"), "debug_log_status missing from tools/list");

  sendMsg(proc.stdin, {
    jsonrpc: "2.0",
    id: "3",
    method: "tools/call",
    params: { name: "debug_create_session", arguments: { program: "src/app/mcp/main.spl" } },
  });
  const createResp = await readMsg();
  const createText = createResp.result.content[0].text;
  const createData = JSON.parse(createText);
  const sessionId = createData.session_id as string;
  assertOk(!!sessionId, "debug_create_session did not return session_id");

  sendMsg(proc.stdin, {
    jsonrpc: "2.0",
    id: "4",
    method: "tools/call",
    params: { name: "debug_list_sessions", arguments: {} },
  });
  const listResp = await readMsg();
  const listText = listResp.result.content[0].text as string;
  assertOk(listText.includes(sessionId), "debug_list_sessions did not include created session");

  sendMsg(proc.stdin, {
    jsonrpc: "2.0",
    id: "5",
    method: "tools/call",
    params: { name: "debug_log_enable", arguments: { pattern: "*" } },
  });
  const enableResp = await readMsg();
  const enableText = enableResp.result.content[0].text as string;
  assertOk(enableText.includes("enabled"), "debug_log_enable did not enable logging");

  sendMsg(proc.stdin, {
    jsonrpc: "2.0",
    id: "6",
    method: "tools/call",
    params: { name: "debug_log_status", arguments: {} },
  });
  const statusResp = await readMsg();
  const statusText = statusResp.result.content[0].text as string;
  assertOk(statusText.includes("\"enabled\":true"), "debug_log_status did not report enabled=true");

  console.log(`typescript probe: OK (session=${sessionId})`);

  sendMsg(proc.stdin, { jsonrpc: "2.0", id: "7", method: "shutdown", params: {} });
  await readMsg();
  proc.kill();
  return 0;
}

main().then(
  (code) => process.exit(code),
  (err) => {
    console.error(`typescript probe: FAIL - ${err.message}`);
    process.exit(1);
  },
);
