// Simple language registration for CodeMirror 6, backed by the generated
// grammar in ./generated/cm6_simple_grammar.ts (see
// scripts/gen_cm6_grammar.mjs at the repo root).
import { LanguageSupport } from "@codemirror/language";
import { simpleCm6Language } from "./generated/cm6_simple_grammar";

export const SIMPLE_LANGUAGE_NAME = "simple";
export const SIMPLE_MIME_TYPE = "text/x-simple";
export const SIMPLE_FILE_EXTENSIONS = [".spl"];

export function simpleLanguage(): LanguageSupport {
  return new LanguageSupport(simpleCm6Language);
}
