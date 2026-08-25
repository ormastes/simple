import { normalizeText } from "../core/identity.js";

function freeze(value, seen = new WeakSet()) {
  if (!value || typeof value !== "object" || seen.has(value)) return value;
  seen.add(value);
  for (const child of Object.values(value)) freeze(child, seen);
  return Object.freeze(value);
}

function diagnostic(code, severity, messageKey, details = {}) {
  return freeze({ code, severity, message_key: messageKey, details: freeze({ ...details }) });
}

function splitTopLevel(value, delimiter = ",") {
  const result = [];
  let start = 0;
  let quote = "";
  let escaped = false;
  let square = 0;
  let curly = 0;
  for (let i = 0; i < value.length; i += 1) {
    const char = value[i];
    if (quote) {
      if (escaped) escaped = false;
      else if (char === "\\") escaped = true;
      else if (char === quote) quote = "";
      continue;
    }
    if (char === '"' || char === "'") { quote = char; continue; }
    if (char === "[") square += 1;
    else if (char === "]") square -= 1;
    else if (char === "{") curly += 1;
    else if (char === "}") curly -= 1;
    else if (char === delimiter && square === 0 && curly === 0) {
      result.push(value.slice(start, i));
      start = i + 1;
    }
  }
  result.push(value.slice(start));
  return result;
}

function stripComment(value) {
  let quote = "";
  let escaped = false;
  for (let i = 0; i < value.length - 1; i += 1) {
    const char = value[i];
    if (quote) {
      if (escaped) escaped = false;
      else if (char === "\\") escaped = true;
      else if (char === quote) quote = "";
      continue;
    }
    if (char === '"' || char === "'") quote = char;
    else if (char === "#" && (i === 0 || /\s/.test(value[i - 1]))) return value.slice(0, i).trimEnd();
  }
  return value;
}

export function parseInlineValue(raw) {
  const value = stripComment(normalizeText(raw));
  if (!value) return "";
  if (value === "null" || value === "nil") return null;
  if (value === "true") return true;
  if (value === "false") return false;
  if (/^-?(?:0|[1-9]\d*)(?:\.\d+)?$/.test(value)) return Number(value);
  if ((value.startsWith('"') && value.endsWith('"')) || (value.startsWith("'") && value.endsWith("'"))) {
    if (value[0] === '"') {
      try { return JSON.parse(value); } catch { return value.slice(1, -1); }
    }
    return value.slice(1, -1).replaceAll("\\'", "'").replaceAll("\\\\", "\\");
  }
  if (value.startsWith("[") && value.endsWith("]")) {
    const inner = value.slice(1, -1).trim();
    return inner ? splitTopLevel(inner).map(parseInlineValue) : [];
  }
  if (value.startsWith("{") && value.endsWith("}")) {
    const inner = value.slice(1, -1).trim();
    const object = {};
    if (!inner) return object;
    for (const part of splitTopLevel(inner)) {
      const separator = part.indexOf(":");
      if (separator < 0) continue;
      const key = normalizeText(part.slice(0, separator)).replace(/^['"]|['"]$/g, "");
      object[key] = parseInlineValue(part.slice(separator + 1));
    }
    return object;
  }
  return value;
}

function keyValue(value) {
  let quote = "";
  let escaped = false;
  let square = 0;
  let curly = 0;
  for (let i = 0; i < value.length; i += 1) {
    const char = value[i];
    if (quote) {
      if (escaped) escaped = false;
      else if (char === "\\") escaped = true;
      else if (char === quote) quote = "";
      continue;
    }
    if (char === '"' || char === "'") quote = char;
    else if (char === "[") square += 1;
    else if (char === "]") square -= 1;
    else if (char === "{") curly += 1;
    else if (char === "}") curly -= 1;
    else if (char === ":" && square === 0 && curly === 0) return i;
  }
  return -1;
}

function setValue(container, key, value, diagnostics, lineNumber) {
  if (Object.hasOwn(container, key)) {
    diagnostics.push(diagnostic("SPK003", "error", "schema.duplicate_key", { key, line: lineNumber }));
    return;
  }
  container[key] = value;
}

/** Parse the deliberately small, deterministic SDN subset used by schemas. */
export function parseSdnDocument(input, options = {}) {
  const source = String(input ?? "").replaceAll("\r\n", "\n").replaceAll("\r", "\n");
  const lines = source.split("\n");
  const root = {};
  const diagnostics = [];
  const stack = [{ indent: -1, value: root }];
  const maxDepth = Number.isInteger(options.maxDepth) ? options.maxDepth : 64;
  let pending = null;

  const nextSignificant = (index) => {
    for (let i = index + 1; i < lines.length; i += 1) {
      const candidate = lines[i].trim();
      if (candidate && !candidate.startsWith("#")) return { indent: lines[i].match(/^\s*/)[0].length, text: candidate };
    }
    return null;
  };

  lines.forEach((line, index) => {
    const lineNumber = index + 1;
    if (!line.trim() || line.trim().startsWith("#")) return;
    const indent = line.match(/^\s*/)[0].length;
    const body = stripComment(line.slice(indent)).trim();
    if (!body) return;
    while (stack.length > 1 && indent <= stack.at(-1).indent) stack.pop();
    const parent = stack.at(-1).value;
    if (stack.length > maxDepth) {
      diagnostics.push(diagnostic("SPK004", "error", "schema.max_depth", { line: lineNumber, max_depth: maxDepth }));
      return;
    }
    if (body.startsWith("- ") || body === "-") {
      if (!Array.isArray(parent)) {
        diagnostics.push(diagnostic("SPK005", "error", "schema.sequence_parent", { line: lineNumber }));
        return;
      }
      const rest = body.slice(1).trim();
      const separator = keyValue(rest);
      if (separator >= 0) {
        const object = {};
        parent.push(object);
        const key = normalizeText(rest.slice(0, separator));
        setValue(object, key, parseInlineValue(rest.slice(separator + 1)), diagnostics, lineNumber);
        stack.push({ indent, value: object });
      } else if (rest) parent.push(parseInlineValue(rest));
      else {
        const child = [];
        parent.push(child);
        stack.push({ indent, value: child });
      }
      return;
    }
    const separator = keyValue(body);
    if (separator < 0) {
      diagnostics.push(diagnostic("SPK006", "error", "schema.expected_key_value", { line: lineNumber }));
      return;
    }
    const key = normalizeText(body.slice(0, separator));
    if (!key) {
      diagnostics.push(diagnostic("SPK007", "error", "schema.empty_key", { line: lineNumber }));
      return;
    }
    const rawValue = body.slice(separator + 1).trim();
    if (rawValue) {
      setValue(parent, key, parseInlineValue(rawValue), diagnostics, lineNumber);
      return;
    }
    const next = nextSignificant(index);
    const child = next && next.indent > indent && next.text.startsWith("-") ? [] : {};
    setValue(parent, key, child, diagnostics, lineNumber);
    stack.push({ indent, value: child });
  });
  return freeze({ value: root, document: root, diagnostics: diagnostics.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b))) });
}

export const parseSdn = parseSdnDocument;

export function parseMetadataAttributes(input) {
  let source = normalizeText(input);
  if (source.startsWith("{") && source.endsWith("}")) {
    const parsed = parseInlineValue(source);
    return parsed && typeof parsed === "object" && !Array.isArray(parsed) ? parsed : {};
  }
  const result = {};
  let token = "";
  let quote = "";
  let escaped = false;
  let square = 0;
  let curly = 0;
  const tokens = [];
  const flush = () => { if (token.trim()) tokens.push(token.trim()); token = ""; };
  for (const char of source) {
    if (quote) {
      token += char;
      if (escaped) escaped = false;
      else if (char === "\\") escaped = true;
      else if (char === quote) quote = "";
    } else if (char === '"' || char === "'") { quote = char; token += char; }
    else if (char === "[") { square += 1; token += char; }
    else if (char === "]") { square -= 1; token += char; }
    else if (char === "{") { curly += 1; token += char; }
    else if (char === "}") { curly -= 1; token += char; }
    else if (/\s/.test(char) && square === 0 && curly === 0) flush();
    else token += char;
  }
  flush();
  for (const item of tokens) {
    const colon = keyValue(item);
    const equals = item.indexOf("=");
    const separator = equals >= 0 && (colon < 0 || equals < colon) ? equals : colon;
    if (separator < 0) continue;
    result[normalizeText(item.slice(0, separator))] = parseInlineValue(item.slice(separator + 1));
  }
  return result;
}
