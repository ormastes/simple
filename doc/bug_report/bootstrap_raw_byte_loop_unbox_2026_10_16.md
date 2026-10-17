# Raw byte loop is decoded as tagged integer during bootstrap

Status: source workaround; executable verification pending; bug DB reconciliation pending qualified tooling.

Manually linked Phase2 ADD1A6782BC0DB64A4BF10285DD72396E8B65387CB11ABA83D29A5AA74A8ADC3 rejects ordinary src/compiler roots in both parse warm-up publication and final-worker source loading. External native selector probe links the exact retained mod_944.o and selected runtime, reports first_byte_word=115 valid=0, exit0. COFF relocation/disassembly shows rt_array_get followed by rt_value_unbox_int in the root validator byte loop. rt_text_to_bytes creates raw packed byte storage; byte112 ('p') is decoded as tagged integer14 and therefore appears to be a forbidden control. Runtime unbox semantics are correct for tagged integers and must not be globally weakened.

Use text codepoint iteration for this lexical validator, rejecting characters lexically below space and exact DEL. All C0 controls and DEL are single codepoints; ordinary Unicode and controls after multibyte text retain the existing policy. Root bytes are not normalized, reordered or broadened. Regression adds ordinary names containing divisible-by-eight ASCII bytes and DEL after Unicode; previous newline/CR/tab/escape checks remain.

Actual compiler/runtime array iteration owner repair remains pending. Existing producer root probe is failure evidence, not patched-source qualification. Original source recovery ba9f1a11d61. Do not apply this workaround to arithmetic or generic byte-array semantics elsewhere without separate owner proof. Phase3 and enum-wire exhausted lanes stay exhausted.
