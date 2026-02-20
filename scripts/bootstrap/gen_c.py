#!/usr/bin/env python3
"""Bootstrap Simple-to-C code generator (pure Python).

Translates Simple language (.spl) source to C code for bootstrapping.
This is a text-level translator that processes source line by line.

Usage:
    python3 scripts/bootstrap/gen_c.py <input.spl> [output.c]
    python3 scripts/bootstrap/gen_c.py --multi <file1.spl> ... --out output.c
"""

import sys
import os
import re

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, '..', '..'))
RUNTIME_PATH = os.path.join(PROJECT_ROOT, 'src', 'app', 'compile', 'c_runtime.c')

# ============================================================
# Type Registry
# ============================================================
# Format: ";text:name;arr:name;fn_text:funcname;struct:Name;"
# Used to track variable types through the translation.

def is_text_var(name, types):
    return f";text:{name};" in types

def is_string_array_var(name, types):
    return f";arr:{name};" in types

def is_int_array_var(name, types):
    return f";int_arr:{name};" in types

def is_fn_returning_text(name, types):
    return f";fn_text:{name};" in types

def is_fn_returning_struct(name, types):
    marker = f";fn_struct:{name}="
    pos = types.find(marker)
    if pos < 0:
        return ""
    after = types[pos + len(marker):]
    end = after.find(";")
    return after[:end] if end >= 0 else ""

def is_struct_type_var(name, types):
    marker = f";struct_var:{name}="
    pos = types.find(marker)
    if pos < 0:
        return ""
    after = types[pos + len(marker):]
    end = after.find(";")
    return after[:end] if end >= 0 else ""

def is_known_struct(name, types):
    return f";struct:{name};" in types

def is_dict_var(name, types):
    return f";dict:{name};" in types

def is_option_var(name, types):
    return f";option:{name};" in types

def is_struct_array_var(name, types):
    marker = f";struct_arr_var:{name}="
    pos = types.find(marker)
    if pos < 0:
        return ""
    after = types[pos + len(marker):]
    end = after.find(";")
    return after[:end] if end >= 0 else ""

def is_fn_returning_int_arr(name, types):
    return f";fn_int_arr:{name};" in types

def is_fn_returning_str_arr(name, types):
    return f";fn_str_arr:{name};" in types

def is_fn_returning_struct_arr(name, types):
    marker = f";fn_struct_arr:{name}="
    pos = types.find(marker)
    if pos < 0:
        return ""
    after = types[pos + len(marker):]
    end = after.find(";")
    return after[:end] if end >= 0 else ""

def is_known_method(class_name, method_name, types):
    return (f";method:{class_name}.{method_name};" in types or
            f";me_method:{class_name}.{method_name};" in types)

def is_me_method(class_name, method_name, types):
    return f";me_method:{class_name}.{method_name};" in types

def is_static_fn(class_name, method_name, types):
    return f";static_fn:{class_name}.{method_name};" in types

def is_enum_variant(dotted, types):
    return f";enum_variant:{dotted};" in types

def resolve_enum_variant(short_name, types):
    search = f".{short_name};"
    pos = types.find(search)
    if pos < 0:
        return ""
    before = types[:pos]
    marker_pos = before.rfind(";enum_variant:")
    if marker_pos < 0:
        return ""
    entry = before[marker_pos + 14:]
    return f"{entry}_{short_name}"

def is_struct_field_text(dotted, types):
    dot_pos = dotted.find(".")
    if dot_pos < 0:
        return False
    obj = dotted[:dot_pos].strip()
    field = dotted[dot_pos + 1:].strip()
    class_name = is_struct_type_var(obj, types)
    if not class_name:
        return False
    return f";field_text:{class_name}.{field};" in types

def is_struct_field_str_array(dotted, types):
    dot_pos = dotted.find(".")
    if dot_pos < 0:
        return False
    obj = dotted[:dot_pos].strip()
    field = dotted[dot_pos + 1:].strip()
    class_name = is_struct_type_var(obj, types)
    if not class_name:
        return False
    return f";field_arr:{class_name}.{field};" in types

def is_struct_field_int_array(dotted, types):
    dot_pos = dotted.find(".")
    if dot_pos < 0:
        return False
    obj = dotted[:dot_pos].strip()
    field = dotted[dot_pos + 1:].strip()
    class_name = is_struct_type_var(obj, types)
    if not class_name:
        return False
    return f";field_int_arr:{class_name}.{field};" in types

def is_struct_field_struct_array(dotted, types):
    dot_pos = dotted.find(".")
    if dot_pos < 0:
        return ""
    obj = dotted[:dot_pos].strip()
    field = dotted[dot_pos + 1:].strip()
    class_name = is_struct_type_var(obj, types)
    if not class_name:
        return ""
    marker = f";field_struct_arr:{class_name}.{field}="
    pos = types.find(marker)
    if pos < 0:
        return ""
    after = types[pos + len(marker):]
    end = after.find(";")
    return after[:end] if end >= 0 else ""


# ============================================================
# Type Conversion
# ============================================================

def simple_type_to_c(stype):
    stype = stype.strip()
    # Strip generic parameters: Option<T> → Option, List<T> → List
    if "<" in stype:
        base = stype[:stype.find("<")].strip()
        if base in ("Option", "Optional"):
            return "void*"
        if base in ("List", "Array"):
            return "SimpleStringArray"
        if base in ("Dict", "Map"):
            return "SimpleDict"
        stype = base  # strip generic for custom types
    # Strip trailing ? for optional types (i64?, text? → just use the base type)
    if stype.endswith("?"):
        stype = stype[:-1]
    if stype in ("i64", "int", "Int"):
        return "long long"
    if stype == "i32":
        return "int"
    if stype in ("f64", "float", "Float"):
        return "double"
    if stype == "f32":
        return "float"
    if stype in ("bool", "Bool"):
        return "int"
    if stype in ("text", "str", "String"):
        return "const char*"
    if stype in ("void", "Void", "Unit", "()"):
        return "void"
    if stype == "Result":
        return "long long"
    if stype == "Any":
        return "void*"
    if stype in ("[text]", "[str]"):
        return "SimpleStringArray"
    if stype in ("[i64]", "[int]", "[bool]"):
        return "SimpleIntArray"
    if stype in ("[[text]]", "[[str]]"):
        return "SimpleStringArrayArray"
    if stype in ("[[i64]]", "[[int]]"):
        return "SimpleIntArrayArray"
    if stype.startswith("[") and stype.endswith("]"):
        inner = stype[1:-1].strip()
        if inner and inner[0].isupper():
            return "SimpleStructArray"
    if stype in ("Option", "Optional"):
        return "void*"
    if stype and stype[0].isupper():
        return stype
    return "long long"


def translate_params(params_str):
    params = params_str.split(",")
    c_parts = []
    for param in params:
        p = param.strip()
        colon_idx = p.find(":")
        if colon_idx >= 0:
            pname = p[:colon_idx].strip()
            ptype = p[colon_idx + 1:].strip()
            ctype = simple_type_to_c(ptype)
            c_parts.append(f"{ctype} {pname}")
        else:
            c_parts.append(f"long long {p}")
    return ", ".join(c_parts)


def parse_fn_signature(trimmed):
    """Parse 'fn name(params) -> ret:' into [name, c_sig, forward_decl]."""
    without_fn = trimmed[3:]  # remove "fn "
    sig = without_fn[:-1].strip()  # remove trailing ":"

    # Strip generic type parameters: fn name<T>(params) → fn name(params)
    gen_start = sig.find("<")
    if gen_start >= 0:
        gen_end = sig.find(">", gen_start)
        if gen_end >= 0 and gen_end < sig.find("("):
            sig = sig[:gen_start] + sig[gen_end + 1:]

    paren_idx = sig.find("(")
    if paren_idx < 0:
        return [sig, f"long long {sig}(void)", f"long long {sig}(void);"]

    name = sig[:paren_idx].strip()

    arrow_idx = sig.find("->")
    ret_type = "void"
    if arrow_idx >= 0:
        ret_str = sig[arrow_idx + 2:].strip()
        ret_type = simple_type_to_c(ret_str)

    close_paren = sig.find(")")
    params_str = ""
    if close_paren > paren_idx + 1:
        params_str = sig[paren_idx + 1:close_paren].strip()

    c_params = "void"
    if params_str:
        c_params = translate_params(params_str)

    c_sig = f"{ret_type} {name}({c_params})"
    return [name, c_sig, f"{c_sig};"]


# ============================================================
# Expression Translation
# ============================================================

def find_close_paren(expr, open_pos):
    depth = 1
    i = open_pos + 1
    in_str = False
    while i < len(expr):
        ch = expr[i]
        if ch == '"' and (i == 0 or expr[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0:
                    return i
        i += 1
    return -1


def translate_expr(expr, types, _depth=0):
    """Translate a Simple expression to C."""
    if _depth > 30:
        return expr  # Bail out to prevent infinite recursion
    expr = expr.strip()
    if not expr:
        return "0"

    # nil
    if expr == "nil":
        return "NULL"
    # true/false
    if expr == "true":
        return "1"
    if expr == "false":
        return "0"
    # Raw string literal: r"..." → treat as regular string (no interpolation)
    if expr.startswith('r"'):
        close_q = _find_close_quote(expr, 1)  # start after 'r'
        if close_q >= 0 and close_q == len(expr) - 1:
            return expr[1:]  # Strip the 'r' prefix, keep the quoted string

    # String literal - check it's a single string, not "a" + "b"
    if expr.startswith('"'):
        close_q = _find_close_quote(expr, 0)
        if close_q >= 0 and close_q == len(expr) - 1:
            return translate_string_literal(expr, types)
    # Integer literal (strip underscore separators: 1_000 → 1000)
    if re.match(r'^-?\d[\d_]*$', expr):
        return expr.replace("_", "")
    # Float literal (strip underscores)
    if re.match(r'^-?\d[\d_]*\.\d[\d_]*$', expr):
        return expr.replace("_", "")
    # Array literal []
    if expr == "[]":
        return "simple_new_string_array()"
    # Parenthesized expression — only if the open paren matches the close paren
    if expr.startswith("(") and expr.endswith(")"):
        close = find_close_paren(expr, 0)
        if close == len(expr) - 1:
            inner = expr[1:-1].strip()
            return f"({translate_expr(inner, types, _depth + 1)})"
    # not prefix
    if expr.startswith("not "):
        inner = expr[4:]
        return f"!({translate_condition(inner, types)})"
    # Lambda: \x: expr or \x, y: expr
    if expr.startswith("\\"):
        return "NULL /* lambda */"
    # Lambda: fn(): expr or fn(x): expr
    if expr.startswith("fn(") or expr.startswith("fn ():") or expr.startswith("fn():"):
        return "NULL /* lambda */"
    # ?? null coalescing (use string-aware splitting)
    _nq_parts = _split_top_level_str(expr, " ?? ")
    if len(_nq_parts) >= 2:
        left_nq = _nq_parts[0].strip()
        right_nq = " ?? ".join(_nq_parts[1:]).strip()
        c_left = translate_expr(left_nq, types)
        c_right = translate_expr(right_nq, types)
        # Text null coalescing
        if is_text_var(left_nq, types) or right_nq.startswith('"'):
            return f"({c_left} != NULL ? {c_left} : {c_right})"
        return f"({c_left} >= 0 ? {c_left} : {c_right})"
    # Boolean operators (lowest precedence, check first)
    _or_parts = _split_top_level_str(expr, " or ")
    if len(_or_parts) >= 2:
        left = _or_parts[0].strip()
        right = " or ".join(_or_parts[1:]).strip()
        return f"({translate_expr(left, types, _depth + 1)} || {translate_expr(right, types, _depth + 1)})"
    _and_parts = _split_top_level_str(expr, " and ")
    if len(_and_parts) >= 2:
        left = _and_parts[0].strip()
        right = " and ".join(_and_parts[1:]).strip()
        return f"({translate_expr(left, types, _depth + 1)} && {translate_expr(right, types, _depth + 1)})"
    # Comparison operators (use string+paren-aware splitting)
    for op in [" == ", " != ", " >= ", " <= ", " > ", " < "]:
        _cmp_parts = _split_top_level_str(expr, op)
        if len(_cmp_parts) >= 2:
            left = _cmp_parts[0].strip()
            right = op.join(_cmp_parts[1:]).strip()
            c_left = translate_expr(left, types, _depth + 1)
            c_right = translate_expr(right, types, _depth + 1)
            # String comparison
            if (left.startswith('"') or right.startswith('"') or
                is_text_var(left, types) or is_text_var(right, types) or
                is_text_expression(left, types) or is_text_expression(right, types)):
                if op == " == ":
                    return f"strcmp({c_left}, {c_right}) == 0"
                elif op == " != ":
                    return f"strcmp({c_left}, {c_right}) != 0"
                c_op = op.strip()
                return f"strcmp({c_left}, {c_right}) {c_op} 0"
            return f"{c_left}{op}{c_right}"
    # String concatenation with + (use string+paren-aware splitting)
    _plus_parts = _split_top_level_str(expr, " + ")
    if len(_plus_parts) >= 2:
        left = _plus_parts[0].strip()
        right = " + ".join(_plus_parts[1:]).strip()
        c_left = translate_expr(left, types, _depth + 1)
        c_right = translate_expr(right, types, _depth + 1)
        if (left.startswith('"') or is_text_var(left, types) or
            is_text_expression(left, types) or
            right.startswith('"') or is_text_var(right, types) or
            is_text_expression(right, types)):
            return f"simple_str_concat({c_left}, {c_right})"
        return f"{c_left} + {c_right}"
    # Bitwise xor
    _xor_parts = _split_top_level_str(expr, " xor ")
    if len(_xor_parts) >= 2:
        left = _xor_parts[0].strip()
        right = " xor ".join(_xor_parts[1:]).strip()
        return f"({translate_expr(left, types, _depth + 1)} ^ {translate_expr(right, types, _depth + 1)})"
    # Type cast: expr as Type → (CType)(expr)
    _as_parts = _split_top_level_str(expr, " as ")
    if len(_as_parts) == 2:
        cast_expr = _as_parts[0].strip()
        cast_type = _as_parts[1].strip()
        c_cast_type = simple_type_to_c(cast_type)
        c_cast_expr = translate_expr(cast_expr, types, _depth + 1)
        return f"({c_cast_type})({c_cast_expr})"
    # Arithmetic
    for op in [" - ", " * ", " / ", " % "]:
        _arith_parts = _split_top_level_str(expr, op)
        if len(_arith_parts) >= 2:
            left = _arith_parts[0].strip()
            right = _arith_parts[1].strip()
            return f"{translate_expr(left, types, _depth + 1)}{op}{translate_expr(right, types, _depth + 1)}"
    # Slice/indexing: s[start:end] or arr[idx] — check BEFORE method calls
    # because expressions like result[pattern.len():] have dots and parens inside brackets
    if "[" in expr and expr.endswith("]") and not expr.startswith("["):
        bracket_pos = _find_bracket_pos(expr)
        if bracket_pos >= 0 and bracket_pos > 0:
            base = expr[:bracket_pos].strip()
            close_bracket = _find_close_bracket(expr, bracket_pos)
            if close_bracket >= 0 and close_bracket == len(expr) - 1:
                idx_expr = expr[bracket_pos + 1:close_bracket].strip()
                _slice_parts = _split_top_level_str(idx_expr, ":")
                if len(_slice_parts) == 2:
                    start_s = _slice_parts[0].strip()
                    end_s = _slice_parts[1].strip()
                    c_base = translate_expr(base, types, _depth + 1)
                    c_start = translate_expr(start_s, types, _depth + 1) if start_s else "0"
                    c_end = translate_expr(end_s, types, _depth + 1) if end_s else f"simple_strlen({c_base})"
                    return f"simple_substring({c_base}, {c_start}, {c_end})"
                # Array indexing
                c_idx = translate_expr(idx_expr, types, _depth + 1)
                if is_text_var(base, types):
                    return f"simple_char_at({base}, {c_idx})"
                if is_string_array_var(base, types):
                    return f"{base}.items[{c_idx}]"
                if is_int_array_var(base, types):
                    return f"{base}.items[{c_idx}]"
                if is_dict_var(base, types):
                    return f"simple_dict_get({base}, {c_idx})"
                return f"{base}.items[{c_idx}]"
    # Method calls: obj.method(args) — handle chaining after the call
    if "." in expr and "(" in expr:
        mc_paren = expr.find("(")
        mc_close = find_close_paren(expr, mc_paren)
        if mc_close >= 0 and mc_close < len(expr) - 1:
            mc_rest = expr[mc_close + 1:].strip()
            if mc_rest:
                base_expr = expr[:mc_close + 1]
                c_base = translate_method_call(base_expr, types)
                return _translate_chain(c_base, mc_rest, types, _depth)
        return translate_method_call(expr, types)
    # .len property (no parens)
    if expr.endswith(".len"):
        base = expr[:-4]
        if is_string_array_var(base, types) or is_int_array_var(base, types):
            return f"{base}.len"
        # Check struct field arrays (e.g., self.parts.len where parts is [text])
        if is_struct_field_str_array(base, types) or is_struct_field_int_array(base, types):
            return f"{translate_expr(base, types)}.len"
        return f"simple_strlen({translate_expr(base, types)})"
    # Field access: obj.field
    if "." in expr:
        dot_pos = expr.rfind(".")
        obj = expr[:dot_pos].strip()
        field = expr[dot_pos + 1:].strip()
        if field.isidentifier():
            # Enum variant: EnumType.Variant → EnumType_TAG_Variant
            if is_enum_variant(f"{obj}.{field}", types):
                return f"{obj}_TAG_{field}"
            # Static function: ClassName.method → ClassName__method
            if is_static_fn(obj, field, types):
                return f"{obj}__{field}"
            c_obj = translate_expr(obj, types)
            # self is a pointer, use -> instead of .
            if obj == "self" or obj.startswith("self.") or c_obj.startswith("self->"):
                return f"self->{field}"
            return f"{c_obj}.{field}"
    # Array literal: [a, b, c] (bracket at position 0, no base)
    if expr.startswith("[") and expr.endswith("]"):
        inner_content = expr[1:-1].strip()
        if not inner_content:
            return "simple_new_string_array()"
        # Build array with pushes — return a block expression via helper variable
        items = split_top_level(inner_content, ",")
        # Check if items look like strings/text
        is_str = any(it.strip().startswith('"') or is_text_var(it.strip(), types) or
                      is_text_expression(it.strip(), types) for it in items)
        if is_str:
            parts = ["({ SimpleStringArray _arr_lit = simple_new_string_array();"]
            for item in items:
                item = item.strip()
                if item:
                    c_item = translate_expr(item, types)
                    parts.append(f" simple_string_push(&_arr_lit, {c_item});")
            parts.append(" _arr_lit; })")
            return "".join(parts)
        else:
            parts = ["({ SimpleIntArray _arr_lit = simple_new_int_array();"]
            for item in items:
                item = item.strip()
                if item:
                    c_item = translate_expr(item, types)
                    parts.append(f" simple_int_push(&_arr_lit, {c_item});")
            parts.append(" _arr_lit; })")
            return "".join(parts)

    # Slice/indexing: s[start:end] or arr[idx]
    if "[" in expr and expr.endswith("]"):
        bracket_pos = _find_bracket_pos(expr)
        if bracket_pos >= 0:
            base = expr[:bracket_pos].strip()
            # Find matching close bracket (respecting parens and strings)
            close_bracket = _find_close_bracket(expr, bracket_pos)
            if close_bracket >= 0:
                idx_expr = expr[bracket_pos + 1:close_bracket].strip()
                # Check for slice syntax (colon inside brackets, not inside strings/parens)
                _slice_parts = _split_top_level_str(idx_expr, ":")
                if len(_slice_parts) == 2:
                    start_s = _slice_parts[0].strip()
                    end_s = _slice_parts[1].strip()
                    c_base = translate_expr(base, types)
                    c_start = translate_expr(start_s, types) if start_s else "0"
                    c_end = translate_expr(end_s, types) if end_s else f"simple_strlen({c_base})"
                    return f"simple_substring({c_base}, {c_start}, {c_end})"
                # Array indexing: arr[idx]
                c_idx = translate_expr(idx_expr, types)
                if is_text_var(base, types):
                    return f"simple_char_at({base}, {c_idx})"
                if is_string_array_var(base, types):
                    return f"{base}.items[{c_idx}]"
                if is_int_array_var(base, types):
                    return f"{base}.items[{c_idx}]"
                if is_dict_var(base, types):
                    return f"simple_dict_get({base}, {c_idx})"
                return f"{base}.items[{c_idx}]"
    # Struct constructor: TypeName(field: value, ...)
    if "(" in expr and expr[0].isupper():
        paren_pos = expr.find("(")
        type_name = expr[:paren_pos].strip()
        if is_known_struct(type_name, types):
            close = find_close_paren(expr, paren_pos)
            if close > 0:
                args_str = expr[paren_pos + 1:close].strip()
                if ":" in args_str:
                    # Named field constructor
                    fields = split_top_level(args_str, ",")
                    field_inits = []
                    for f in fields:
                        f = f.strip()
                        if ":" in f:
                            fname, fval = f.split(":", 1)
                            c_val = translate_expr(fval.strip(), types, _depth + 1)
                            field_inits.append(f".{fname.strip()} = {c_val}")
                        else:
                            field_inits.append(translate_expr(f, types, _depth + 1))
                    return f"({type_name}){{{', '.join(field_inits)}}}"

    # Function call: name(args)
    if "(" in expr:
        paren_pos = expr.find("(")
        fname = expr[:paren_pos].strip()
        close = find_close_paren(expr, paren_pos)
        if close > 0:
            args = expr[paren_pos + 1:close].strip()
            rest = expr[close + 1:].strip()
            if args:
                c_args = translate_call_args(args, types)
                c_call = f"{fname}({c_args})"
            else:
                c_call = f"{fname}()"
            if rest:
                return _translate_chain(c_call, rest, types, _depth)
            return c_call
    # Simple identifier
    return expr


def _translate_chain(c_obj, rest, types, _depth=0):
    """Handle chained access after an already-translated expression."""
    if not rest or _depth > 30:
        return c_obj
    # .method(args) or .field
    if rest.startswith("."):
        after_dot = rest[1:]
        if "(" in after_dot:
            # Method call chain: .method(args)...
            paren_pos = after_dot.find("(")
            method = after_dot[:paren_pos].strip()
            close = find_close_paren(after_dot, paren_pos)
            if close >= 0:
                m_args_str = after_dot[paren_pos + 1:close].strip()
                after_method = after_dot[close + 1:].strip()
                # Translate common string/array methods
                c_result = _translate_chained_method(c_obj, method, m_args_str, types)
                if after_method:
                    return _translate_chain(c_result, after_method, types, _depth + 1)
                return c_result
        # Field access: .field
        dot_end = 0
        while dot_end < len(after_dot) and (after_dot[dot_end].isalnum() or after_dot[dot_end] == '_'):
            dot_end += 1
        field = after_dot[:dot_end]
        remaining = after_dot[dot_end:]
        if field == "len":
            # If c_obj is an array expression (from split, keys, etc.), use .len
            if "simple_split(" in c_obj or "simple_dict_keys(" in c_obj or "simple_new_" in c_obj:
                return _translate_chain(f"{c_obj}.len", remaining, types, _depth + 1)
            return _translate_chain(f"simple_strlen({c_obj})", remaining, types, _depth + 1)
        return _translate_chain(f"{c_obj}.{field}", remaining, types, _depth + 1)
    # [idx]
    if rest.startswith("["):
        close_bracket = rest.find("]")
        if close_bracket >= 0:
            idx = rest[1:close_bracket]
            after = rest[close_bracket + 1:]
            c_idx = translate_expr(idx, types, _depth + 1)
            return _translate_chain(f"{c_obj}.items[{c_idx}]", after, types, _depth + 1)
    return c_obj + rest  # fallback


def _translate_chained_method(c_obj, method, args_str, types):
    """Translate a method call on an already-translated C expression."""
    if args_str:
        c_args = translate_call_args(args_str, types)
    else:
        c_args = ""

    # String methods
    if method == "contains":
        return f"simple_contains({c_obj}, {c_args})"
    if method in ("starts_with", "startswith"):
        return f"simple_starts_with({c_obj}, {c_args})"
    if method in ("ends_with", "endswith"):
        return f"simple_ends_with({c_obj}, {c_args})"
    if method == "trim":
        return f"simple_trim({c_obj})"
    if method == "index_of":
        return f"simple_index_of({c_obj}, {c_args})"
    if method == "last_index_of":
        return f"simple_last_index_of({c_obj}, {c_args})"
    if method == "replace":
        return f"simple_replace({c_obj}, {c_args})"
    if method == "split":
        return f"simple_split({c_obj}, {c_args})"
    if method == "substring":
        return f"simple_substring({c_obj}, {c_args})"
    if method == "len":
        # If c_obj is an array expression, use .len instead of simple_strlen
        if "simple_split(" in c_obj or "simple_dict_keys(" in c_obj or "simple_new_" in c_obj:
            return f"{c_obj}.len"
        return f"simple_strlen({c_obj})"
    if method == "join":
        return f"simple_string_join(&{c_obj}, {c_args})"
    if method == "push":
        return f"simple_string_push(&{c_obj}, {c_args})"
    if method == "pop":
        return f"simple_string_pop(&{c_obj})"
    if method == "keys":
        return f"simple_dict_keys({c_obj})"
    if method == "remove":
        return f"simple_dict_remove({c_obj}, {c_args})"
    if method == "char_at":
        return f"simple_char_at({c_obj}, {c_args})"
    if method == "slice":
        return f"simple_substring({c_obj}, {c_args})"
    if method == "append":
        return f"simple_string_push(&{c_obj}, {c_args})"
    if method == "insert":
        return f"simple_string_push(&{c_obj}, {c_args})"
    if method == "to_upper":
        return f"simple_to_upper({c_obj})"
    if method == "to_lower":
        return f"simple_to_lower({c_obj})"
    if method == "to_string":
        return f"simple_int_to_str({c_obj})"
    if method == "to_i64" or method == "to_int":
        return f"simple_str_to_int({c_obj})"
    if method == "to_text":
        return f"simple_int_to_str({c_obj})"
    if method == "unwrap":
        return c_obj
    if method == "unwrap_or":
        return f"({c_obj} != 0 ? {c_obj} : {c_args})" if c_args else c_obj
    if method == "is_some":
        return f"({c_obj} != 0)"
    if method == "is_none" or method == "is_nil":
        return f"({c_obj} == 0)"
    if method == "find":
        return f"simple_index_of({c_obj}, {c_args})"
    if method == "format" or method == "fmt":
        return c_obj

    # Generic method call
    if c_args:
        return f"{c_obj}.{method}({c_args})"
    return f"{c_obj}.{method}()"


def is_text_expression(expr, types):
    """Check if an expression evaluates to a text/string type."""
    expr = expr.strip()
    if expr.startswith('"'):
        return True
    if is_text_var(expr, types):
        return True
    # Array indexing of string array: arr[i]
    if "[" in expr and expr.endswith("]"):
        base = expr[:expr.find("[")].strip()
        if is_string_array_var(base, types):
            return True
    # Method calls returning text
    if "." in expr and "(" in expr:
        dot_pos = expr.find(".")
        paren_pos = expr.find("(")
        if dot_pos < paren_pos:
            method = expr[dot_pos+1:paren_pos].strip()
            if method in ("trim", "replace", "substring", "join", "char_at", "slice",
                          "to_upper", "to_lower"):
                return True
    # Function calls returning text
    if "(" in expr:
        fname = expr[:expr.find("(")].strip()
        if is_fn_returning_text(fname, types):
            return True
    # String concatenation
    if " + " in expr:
        parts = split_preserving_strings(expr, " + ")
        if any(p.strip().startswith('"') or is_text_var(p.strip(), types) for p in parts):
            return True
    # Field access on struct (text field)
    if "." in expr and "(" not in expr:
        if is_struct_field_text(expr, types):
            return True
    return False


def translate_condition(cond, types):
    """Translate a condition expression."""
    return translate_expr(cond, types)


def translate_call_args(args_str, types):
    """Translate comma-separated arguments, stripping named arg labels."""
    args = split_top_level(args_str, ",")
    translated = []
    for a in args:
        a = a.strip()
        # Strip named argument: name: value → just value
        # But be careful: "key: value" where key is a simple identifier followed by ':'
        colon_pos = a.find(":")
        if colon_pos > 0 and "(" not in a[:colon_pos] and a[:colon_pos].strip().isidentifier():
            # Check it's not a slice or ternary
            val = a[colon_pos + 1:].strip()
            if val:  # Only strip if there's something after the colon
                translated.append(translate_expr(val, types))
                continue
        translated.append(translate_expr(a, types))
    return ", ".join(translated)


def translate_method_call(expr, types):
    """Translate obj.method(args) to C."""
    # Find the method call pattern
    paren_pos = expr.find("(")
    if paren_pos < 0:
        return expr

    prefix = expr[:paren_pos]
    close = find_close_paren(expr, paren_pos)
    if close < 0:
        return expr

    args = expr[paren_pos + 1:close].strip()
    rest_after_call = expr[close + 1:].strip()

    dot_pos = prefix.rfind(".")
    if dot_pos < 0:
        # Regular function call
        if args:
            c_call = f"{prefix}({translate_call_args(args, types)})"
        else:
            c_call = f"{prefix}()"
        if rest_after_call:
            return _translate_chain(c_call, rest_after_call, types, 0)
        return c_call

    obj = prefix[:dot_pos].strip()
    method = prefix[dot_pos + 1:].strip()
    c_obj = translate_expr(obj, types)

    # String methods
    if method == "contains":
        c_arg = translate_expr(args, types)
        if is_dict_var(obj, types):
            return f"simple_dict_contains({c_obj}, {c_arg})"
        if is_string_array_var(obj, types):
            return f"simple_str_array_contains({c_obj}, {c_arg})"
        return f"simple_contains({c_obj}, {c_arg})"
    if method == "starts_with" or method == "startswith":
        return f"simple_starts_with({c_obj}, {translate_expr(args, types)})"
    if method == "ends_with" or method == "endswith":
        return f"simple_ends_with({c_obj}, {translate_expr(args, types)})"
    if method == "trim":
        return f"simple_trim({c_obj})"
    if method == "index_of":
        return f"simple_index_of({c_obj}, {translate_expr(args, types)})"
    if method == "last_index_of":
        return f"simple_last_index_of({c_obj}, {translate_expr(args, types)})"
    if method == "replace":
        parts = split_top_level(args, ",")
        if len(parts) >= 2:
            return f"simple_replace({c_obj}, {translate_expr(parts[0].strip(), types)}, {translate_expr(parts[1].strip(), types)})"
    if method == "split":
        return f"simple_split({c_obj}, {translate_expr(args, types)})"
    if method == "substring":
        parts = split_top_level(args, ",")
        if len(parts) >= 2:
            return f"simple_substring({c_obj}, {translate_expr(parts[0].strip(), types)}, {translate_expr(parts[1].strip(), types)})"
        return f"simple_substring({c_obj}, {translate_expr(parts[0].strip(), types)}, simple_strlen({c_obj}))"
    if method == "len":
        if is_string_array_var(obj, types) or is_int_array_var(obj, types):
            return f"{c_obj}.len"
        if is_dict_var(obj, types):
            return f"simple_dict_len({c_obj})"
        # Check struct field arrays (e.g. self.parts.len() where parts is [text])
        if is_struct_field_str_array(obj, types) or is_struct_field_int_array(obj, types):
            return f"{c_obj}.len"
        # Check if obj expression returns an array (e.g. x.split(...).len())
        if ".split(" in obj or ".keys(" in obj:
            return f"{c_obj}.len"
        return f"simple_strlen({c_obj})"
    if method == "join":
        c_arg = translate_expr(args, types)
        return f"simple_string_join(&{c_obj}, {c_arg})"
    if method == "push":
        c_arg = translate_expr(args, types)
        if is_string_array_var(obj, types):
            return f"simple_string_push(&{c_obj}, {c_arg})"
        if is_int_array_var(obj, types):
            return f"simple_int_push(&{c_obj}, {c_arg})"
        return f"simple_string_push(&{c_obj}, {c_arg})"
    if method == "pop":
        if is_int_array_var(obj, types):
            return f"simple_int_pop(&{c_obj})"
        return f"simple_string_pop(&{c_obj})"
    if method == "keys":
        return f"simple_dict_keys({c_obj})"
    if method == "remove":
        return f"simple_dict_remove({c_obj}, {translate_expr(args, types)})"
    if method == "slice":
        parts = split_top_level(args, ",")
        if len(parts) >= 2:
            return f"simple_substring({c_obj}, {translate_expr(parts[0].strip(), types)}, {translate_expr(parts[1].strip(), types)})"
        return f"simple_substring({c_obj}, {translate_expr(parts[0].strip(), types)}, simple_strlen({c_obj}))"
    if method == "append":
        c_arg = translate_expr(args, types)
        if is_string_array_var(obj, types):
            return f"simple_string_push(&{c_obj}, {c_arg})"
        if is_int_array_var(obj, types):
            return f"simple_int_push(&{c_obj}, {c_arg})"
        return f"simple_string_push(&{c_obj}, {c_arg})"
    if method == "insert":
        c_arg = translate_expr(args, types)
        return f"simple_string_push(&{c_obj}, {c_arg})"
    if method == "to_upper":
        return f"simple_to_upper({c_obj})"
    if method == "to_lower":
        return f"simple_to_lower({c_obj})"
    if method == "to_string" or method == "to_text":
        return f"simple_int_to_str({c_obj})"
    if method == "to_i64" or method == "to_int":
        return f"simple_str_to_int({c_obj})"
    if method == "unwrap":
        return c_obj
    if method == "unwrap_or":
        if args:
            c_arg = translate_expr(args, types)
            return f"({c_obj} != 0 ? {c_obj} : {c_arg})"
        return c_obj
    if method == "is_some":
        return f"({c_obj} != 0)"
    if method == "is_none" or method == "is_nil":
        return f"({c_obj} == 0)"
    if method == "find":
        return f"simple_index_of({c_obj}, {translate_expr(args, types)})"
    if method == "format" or method == "fmt":
        return c_obj

    # Struct method call
    class_name = is_struct_type_var(obj, types)
    if class_name:
        if is_me_method(class_name, method, types):
            if args:
                return f"{class_name}__{method}(&{c_obj}, {translate_call_args(args, types)})"
            return f"{class_name}__{method}(&{c_obj})"
        if args:
            return f"{class_name}__{method}(&{c_obj}, {translate_call_args(args, types)})"
        return f"{class_name}__{method}(&{c_obj})"

    # Generic method -> try as field access
    if args:
        return f"{c_obj}.{method}({translate_call_args(args, types)})"
    return f"{c_obj}.{method}()"


def translate_string_literal(s, types):
    """Translate a Simple string literal to C, handling interpolation."""
    if s == '""':
        return '""'
    inner = s[1:-1]
    if "{" not in inner:
        return s

    # Handle string interpolation
    parts = []
    fmt_parts = []
    i = 0
    while i < len(inner):
        if inner[i] == '\\' and i + 1 < len(inner):
            fmt_parts.append(inner[i:i+2])
            i += 2
            continue
        # Escaped braces: {{ → literal {, }} → literal }
        if inner[i] == '{' and i + 1 < len(inner) and inner[i + 1] == '{':
            fmt_parts.append('{')
            i += 2
            continue
        if inner[i] == '}' and i + 1 < len(inner) and inner[i + 1] == '}':
            fmt_parts.append('}')
            i += 2
            continue
        if inner[i] == '{':
            j = i + 1
            depth = 0
            while j < len(inner):
                if inner[j] == '}' and depth == 0:
                    break
                if inner[j] == '{':
                    depth += 1
                elif inner[j] == '}':
                    depth -= 1
                j += 1
            if j < len(inner):
                raw_expr = inner[i + 1:j]
                # Skip interpolation for non-expression content (e.g. "{sqrt, abs}")
                # A valid expression should not contain bare commas at top level
                # unless it's a function call
                if raw_expr and "(" not in raw_expr and "," in raw_expr:
                    # Treat as literal braces
                    fmt_parts.append("{")
                    fmt_parts.append(raw_expr)
                    fmt_parts.append("}")
                    i = j + 1
                    continue
                # Check if it's a text expression
                c_expr = translate_expr(raw_expr, types)
                before_str = ''.join(fmt_parts)
                fmt_parts = []
                if before_str:
                    parts.append(f'"{before_str}"')
                parts.append(c_expr)
                i = j + 1
                continue
        fmt_parts.append(inner[i])
        i += 1

    remaining = ''.join(fmt_parts)
    if remaining:
        parts.append(f'"{remaining}"')

    if not parts:
        return '""'
    if len(parts) == 1:
        return parts[0]

    # Concatenate all parts
    result = parts[0]
    for p in parts[1:]:
        result = f"simple_str_concat({result}, {p})"
    return result


# ============================================================
# Utility
# ============================================================

def split_preserving_strings(text, sep):
    """Split text by separator, preserving string literals."""
    parts = []
    current = []
    in_str = False
    i = 0
    while i < len(text):
        if text[i] == '"' and (i == 0 or text[i-1] != '\\'):
            in_str = not in_str
            current.append(text[i])
        elif not in_str and text[i:i+len(sep)] == sep:
            parts.append(''.join(current))
            current = []
            i += len(sep)
            continue
        else:
            current.append(text[i])
        i += 1
    parts.append(''.join(current))
    return parts


def _split_top_level_str(text, sep):
    """Split by multi-char separator, respecting strings, parentheses, and brackets."""
    parts = []
    current = []
    depth = 0
    bracket_depth = 0
    in_str = False
    i = 0
    sep_len = len(sep)
    while i < len(text):
        ch = text[i]
        if ch == '"' and (i == 0 or text[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            elif ch == '[':
                bracket_depth += 1
            elif ch == ']':
                bracket_depth -= 1
            elif depth == 0 and bracket_depth == 0 and text[i:i+sep_len] == sep:
                parts.append(''.join(current))
                current = []
                i += sep_len
                continue
        current.append(ch)
        i += 1
    parts.append(''.join(current))
    return parts


def split_top_level(text, sep):
    """Split by separator, respecting parentheses and strings."""
    parts = []
    current = []
    depth = 0
    in_str = False
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == '"' and (i == 0 or text[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            elif ch == sep and depth == 0:
                parts.append(''.join(current))
                current = []
                i += 1
                continue
        current.append(ch)
        i += 1
    parts.append(''.join(current))
    return parts


def _strip_raw_strings(line):
    """Convert r"..." raw string literals to regular "..." strings.
    Also escape { and } inside raw strings to prevent interpolation."""
    result = []
    i = 0
    while i < len(line):
        if i < len(line) - 1 and line[i] == 'r' and line[i + 1] == '"':
            # Check that 'r' is not part of a word
            if i == 0 or not (line[i - 1].isalnum() or line[i - 1] == '_' or line[i - 1] == '\\'):
                # Found r"..." — skip the 'r', escape { and }
                result.append('"')
                i += 2  # skip r"
                # Copy until close quote, escaping braces
                while i < len(line):
                    if line[i] == '\\' and i + 1 < len(line):
                        result.append(line[i:i+2])
                        i += 2
                        continue
                    if line[i] == '"':
                        result.append('"')
                        i += 1
                        break
                    if line[i] == '{':
                        result.append('{{')
                    elif line[i] == '}':
                        result.append('}}')
                    else:
                        result.append(line[i])
                    i += 1
                continue
        result.append(line[i])
        i += 1
    return ''.join(result)


def _find_bracket_pos(expr):
    """Find the first '[' that is not inside strings or parens (for array indexing/slicing)."""
    in_str = False
    paren_depth = 0
    for i, ch in enumerate(expr):
        if ch == '"' and (i == 0 or expr[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '(':
                paren_depth += 1
            elif ch == ')':
                paren_depth -= 1
            elif ch == '[' and paren_depth == 0:
                return i
    return -1


def _find_close_bracket(expr, open_pos):
    """Find the matching ']' for a '[', respecting strings, parens, and nested brackets."""
    depth = 1
    in_str = False
    i = open_pos + 1
    while i < len(expr):
        ch = expr[i]
        if ch == '"' and (i == 0 or expr[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '[':
                depth += 1
            elif ch == ']':
                depth -= 1
                if depth == 0:
                    return i
            elif ch == '(':
                pass  # parens inside brackets are OK
            elif ch == ')':
                pass  # parens inside brackets are OK
        i += 1
    return -1


def _find_dotdot(expr):
    """Find position of '..' range operator, not inside strings or parens."""
    in_str = False
    paren_depth = 0
    i = 0
    while i < len(expr) - 1:
        ch = expr[i]
        if ch == '"' and (i == 0 or expr[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '(':
                paren_depth += 1
            elif ch == ')':
                paren_depth -= 1
            elif ch == '.' and expr[i + 1] == '.' and paren_depth == 0:
                # Make sure it's not "..." (three dots)
                if i + 2 < len(expr) and expr[i + 2] == '.':
                    i += 1
                    continue
                return i
        i += 1
    return -1


def _find_close_quote(text, start):
    """Find the matching close quote starting from position start (which is the opening quote).
    Properly handles escaped characters including \\\\ (escaped backslash)."""
    i = start + 1
    while i < len(text):
        if text[i] == '\\':
            # Skip the escaped character (handles \\, \", \n, etc.)
            i += 2
            continue
        if text[i] == '"':
            return i
        i += 1
    return -1


def _count_paren_depth(line):
    """Count net parenthesis depth change, respecting string literals."""
    depth = 0
    in_str = False
    for i, ch in enumerate(line):
        if ch == '"' and (i == 0 or line[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            elif ch == '#':
                break  # Rest is comment
    return depth


def _find_comment_start(line):
    """Find the position of a # comment, respecting string literals."""
    in_str = False
    for i, ch in enumerate(line):
        if ch == '"' and (i == 0 or line[i-1] != '\\'):
            in_str = not in_str
        elif ch == '#' and not in_str:
            return i
    return -1


def _find_if_colon(trimmed):
    """Find the colon position in 'if condition: body', respecting strings and parens."""
    i = 3  # skip "if "
    in_str = False
    paren_depth = 0
    while i < len(trimmed):
        ch = trimmed[i]
        if ch == '"' and (i == 0 or trimmed[i-1] != '\\'):
            in_str = not in_str
        elif not in_str:
            if ch == '(':
                paren_depth += 1
            elif ch == ')':
                paren_depth -= 1
            elif ch == ':' and paren_depth == 0:
                return i
        i += 1
    return -1


def get_indent_level(line):
    spaces = 0
    for ch in line:
        if ch == ' ':
            spaces += 1
        elif ch == '\t':
            spaces += 4
        else:
            break
    return spaces // 4


# ============================================================
# Main Code Generator
# ============================================================

def generate_c_code(source_text):
    """Generate C code from Simple source text."""
    types = ";"
    # Pre-seed common variables
    types += "text:par_text;text:par_current;text:lex_cur_text;text:lex_cur_suffix;"
    types += "text:g_log_filter_pattern;"

    raw_lines = source_text.split("\n")

    # Pre-process: convert r"..." raw strings to regular "..." (strip r prefix)
    processed_lines = []
    for rline in raw_lines:
        processed_lines.append(_strip_raw_strings(rline))
    raw_lines = processed_lines

    # Pre-process: join multi-line expressions (unclosed parens, respecting strings)
    lines = []
    pending = ""
    paren_depth = 0
    for rline in raw_lines:
        if pending:
            pending = pending + " " + rline.strip()
        else:
            pending = rline
        paren_depth += _count_paren_depth(rline)
        if paren_depth <= 0:
            lines.append(pending)
            pending = ""
            paren_depth = 0
    if pending:
        lines.append(pending)

    forward_decls = []
    struct_defs = []
    enum_defs = []
    function_bodies = []
    global_constants = []  # Top-level val with literal RHS → global const
    module_vars = []
    main_code = []
    module_init_code = []
    main_indent_stack = []

    i = 0
    in_fn = False
    fn_name = ""
    fn_sig = ""
    fn_orig_line = ""
    fn_body = []
    fn_indent = 0
    in_struct = False
    struct_name = ""
    struct_fields = []
    in_enum = False
    enum_name = ""
    enum_variants = []
    in_class = False
    class_name = ""
    class_methods = []
    skip_block_indent = -1

    while i < len(lines):
        line = lines[i]
        trimmed = line.strip()

        # Skip empty lines and comments
        if not trimmed or trimmed.startswith("#"):
            if in_fn:
                fn_body.append("")
            i += 1
            continue

        # Skip docstrings (triple-quoted strings as standalone statements)
        if trimmed.startswith('"""') or trimmed.startswith("'''"):
            # Skip until closing triple-quote
            if trimmed.endswith('"""') and len(trimmed) > 3:
                # Single-line docstring
                i += 1
                continue
            # Multi-line docstring: skip until closing """
            i += 1
            while i < len(lines):
                if '"""' in lines[i] or "'''" in lines[i]:
                    i += 1
                    break
                i += 1
            continue

        # Strip trailing comments from all lines
        comment_pos = _find_comment_start(trimmed)
        if comment_pos > 0:
            trimmed = trimmed[:comment_pos].rstrip()
            if not trimmed:
                i += 1
                continue

        # Type alias: type X = Y
        if trimmed.startswith("type ") and " = " in trimmed:
            parts = trimmed[5:].split(" = ", 1)
            if len(parts) >= 2:
                alias_name = parts[0].strip()
                target = parts[1].strip()
                c_target = simple_type_to_c(target)
                struct_defs.append(f"typedef {c_target} {alias_name};")
                types += f"struct:{alias_name};"
            i += 1
            continue

        # Alias: alias X = Y
        if trimmed.startswith("alias ") and " = " in trimmed:
            parts = trimmed[6:].split(" = ", 1)
            if len(parts) >= 2:
                alias_name = parts[0].strip()
                target = parts[1].strip()
                c_target = simple_type_to_c(target)
                struct_defs.append(f"typedef {c_target} {alias_name};")
                types += f"struct:{alias_name};"
            i += 1
            continue

        # Skip use/export/extern/import
        if (trimmed.startswith("use ") or trimmed.startswith("export ") or
            trimmed.startswith("extern fn ") or trimmed.startswith("import ")):
            # Track extern fn return types and emit forward declarations
            if trimmed.startswith("extern fn "):
                sig = trimmed[10:]
                paren_idx = sig.find("(")
                arrow_idx = sig.find("->")
                if paren_idx >= 0:
                    ext_name = sig[:paren_idx].strip()
                    # Parse params
                    close_paren = sig.find(")")
                    ext_params_str = sig[paren_idx + 1:close_paren].strip() if close_paren > paren_idx else ""
                    ext_c_params = "void"
                    if ext_params_str:
                        ext_c_params = translate_params(ext_params_str)
                    # Parse return type
                    ext_ret = "long long"
                    if arrow_idx >= 0:
                        ret_str = sig[arrow_idx + 2:].strip()
                        ext_ret = simple_type_to_c(ret_str)
                        if ret_str in ("text", "str", "String"):
                            types += f"fn_text:{ext_name};"
                        elif ret_str.startswith("["):
                            inner = ret_str[1:-1].strip()
                            if inner in ("text", "str"):
                                types += f"fn_str_arr:{ext_name};"
                            elif inner in ("i64", "int"):
                                types += f"fn_int_arr:{ext_name};"
                            elif inner and inner[0].isupper():
                                types += f"fn_struct_arr:{ext_name}={inner};"
                        elif ret_str and ret_str[0].isupper():
                            types += f"fn_struct:{ext_name}={ret_str};"
                    # Emit forward declaration for extern fn
                    forward_decls.append(f"{ext_ret} {ext_name}({ext_c_params});")
            i += 1
            continue

        indent = get_indent_level(line)

        # End of function/struct/class body
        if in_fn and indent <= fn_indent and trimmed:
            # Emit collected function
            emit_function(fn_name, fn_sig, fn_orig_line, fn_body, forward_decls, function_bodies, types)
            in_fn = False
            fn_body = []
            # Don't increment i - reprocess this line

        if in_struct and indent <= 0 and trimmed and not trimmed.startswith("    "):
            # End of struct
            sdef = f"typedef struct {{\n"
            for sf in struct_fields:
                sdef += f"    {sf}\n"
            sdef += f"}} {struct_name};\n"
            struct_defs.append(sdef)
            types += f"struct:{struct_name};"
            in_struct = False
            struct_fields = []

        if in_enum and indent <= 0 and trimmed and not trimmed.startswith("    "):
            # End of enum - emit
            emit_enum(enum_name, enum_variants, enum_defs, types)
            in_enum = False
            enum_variants = []

        if in_class and indent <= 0 and trimmed:
            in_class = False

        # Function definition (not inside a struct — struct methods handled below)
        if trimmed.startswith("fn ") and trimmed.endswith(":") and not in_struct:
            parsed = parse_fn_signature(trimmed)
            fn_name = parsed[0]
            fn_sig = parsed[1]
            fn_orig_line = trimmed
            forward_decls.append(parsed[2])
            in_fn = True
            fn_indent = indent
            fn_body = []

            # Track return type
            arrow_idx = trimmed.find("->")
            if arrow_idx >= 0:
                ret_str = trimmed[arrow_idx + 2:].strip().rstrip(":")
                if ret_str in ("text", "str", "String"):
                    types += f"fn_text:{fn_name};"
                elif ret_str.startswith("["):
                    inner = ret_str[1:-1].strip()
                    if inner in ("text", "str"):
                        types += f"fn_str_arr:{fn_name};"
                    elif inner in ("i64", "int"):
                        types += f"fn_int_arr:{fn_name};"
                    elif inner and inner[0].isupper():
                        types += f"fn_struct_arr:{fn_name}={inner};"
                elif ret_str and ret_str[0].isupper():
                    types += f"fn_struct:{fn_name}={ret_str};"

            i += 1
            continue

        # Struct definition
        if trimmed.startswith("class ") and trimmed.endswith(":"):
            struct_name = trimmed[6:-1].strip()
            if "(" in struct_name:
                struct_name = struct_name[:struct_name.find("(")].strip()
            in_struct = True
            struct_fields = []
            types += f"struct:{struct_name};"
            i += 1
            continue

        # Enum definition
        if trimmed.startswith("enum ") and trimmed.endswith(":"):
            enum_name = trimmed[5:-1].strip()
            in_enum = True
            enum_variants = []
            i += 1
            continue

        # Inside struct body (but not inside a method body)
        if in_struct and indent > 0 and not in_fn:
            # Method definition inside class: fn name(...) or me name(...)
            if (trimmed.startswith("fn ") or trimmed.startswith("me ")) and trimmed.endswith(":"):
                is_me = trimmed.startswith("me ")
                # Convert to a free function: ClassName__method_name(self, ...)
                method_line = trimmed[3:] if trimmed.startswith("fn ") else trimmed[3:]
                # Parse the method signature
                paren_idx = method_line.find("(")
                colon_end = method_line.rfind(":")
                if paren_idx >= 0:
                    method_name = method_line[:paren_idx].strip()
                    # Build the free function signature with self parameter
                    close_paren = method_line.find(")")
                    params = method_line[paren_idx + 1:close_paren].strip() if close_paren > paren_idx else ""
                    arrow_idx = method_line.find("->")
                    ret_str = "void"
                    if arrow_idx >= 0:
                        ret_str = simple_type_to_c(method_line[arrow_idx + 2:colon_end].strip())

                    self_type = f"{struct_name}*" if is_me else f"const {struct_name}*"
                    if params:
                        c_params = f"{self_type} self, {translate_params(params)}"
                    else:
                        c_params = f"{self_type} self"

                    fn_name_full = f"{struct_name}__{method_name}"
                    fn_sig_full = f"{ret_str} {fn_name_full}({c_params})"
                    forward_decls.append(f"{fn_sig_full};")

                    # Track method
                    if is_me:
                        types += f"me_method:{struct_name}.{method_name};"
                    else:
                        types += f"method:{struct_name}.{method_name};"

                    # Track return type
                    if arrow_idx >= 0:
                        ret_simple = method_line[arrow_idx + 2:colon_end].strip()
                        if ret_simple in ("text", "str"):
                            types += f"fn_text:{fn_name_full};"
                        elif ret_simple.startswith("["):
                            inner = ret_simple[1:-1].strip()
                            if inner in ("text", "str"):
                                types += f"fn_str_arr:{fn_name_full};"
                            elif inner in ("i64", "int"):
                                types += f"fn_int_arr:{fn_name_full};"

                    # Enter function collection mode
                    in_fn = True
                    fn_name = fn_name_full
                    fn_sig = fn_sig_full
                    # Include self in the orig_line so _extract_param_types picks up its type
                    if params:
                        fn_orig_line = f"fn {fn_name_full}(self: {struct_name}, {params}):"
                    else:
                        fn_orig_line = f"fn {fn_name_full}(self: {struct_name}):"
                    fn_indent = indent
                    fn_body = []
                    i += 1
                    continue
            # Static method: static fn name(...)
            elif trimmed.startswith("static fn ") and trimmed.endswith(":"):
                static_line = "fn " + trimmed[10:]
                parsed = parse_fn_signature(static_line)
                static_fn_name = f"{struct_name}__{parsed[0]}"
                # Rebuild signature with class prefix
                arrow_idx = static_line.find("->")
                paren_idx = static_line.find("(")
                close_paren = static_line.find(")")
                params = static_line[paren_idx + 1:close_paren].strip() if close_paren > paren_idx else ""
                ret_type = "void"
                if arrow_idx >= 0:
                    ret_type = simple_type_to_c(static_line[arrow_idx + 2:].rstrip(":").strip())
                c_params = translate_params(params) if params else "void"
                fn_sig_full = f"{ret_type} {static_fn_name}({c_params})"
                forward_decls.append(f"{fn_sig_full};")
                types += f"static_fn:{struct_name}.{parsed[0]};"

                in_fn = True
                fn_name = static_fn_name
                fn_sig = fn_sig_full
                fn_orig_line = static_line
                fn_indent = indent
                fn_body = []
                i += 1
                continue
            elif ":" in trimmed:
                # Field definition
                clean = trimmed.split("#")[0].strip()  # Remove comments
                colon_pos = clean.find(":")
                if colon_pos >= 0:
                    fname = clean[:colon_pos].strip()
                    ftype = clean[colon_pos + 1:].strip()
                    # Skip if it looks like a default value
                    if " = " in ftype:
                        ftype = ftype[:ftype.find(" = ")].strip()
                    c_type = simple_type_to_c(ftype)
                    struct_fields.append(f"{c_type} {fname};")
                    # Track field types
                    if ftype in ("text", "str", "String"):
                        types += f"field_text:{struct_name}.{fname};"
                    elif ftype in ("[text]", "[str]"):
                        types += f"field_arr:{struct_name}.{fname};"
                    elif ftype in ("[i64]", "[int]"):
                        types += f"field_int_arr:{struct_name}.{fname};"
                    elif ftype.startswith("[") and ftype.endswith("]"):
                        inner = ftype[1:-1].strip()
                        if inner and inner[0].isupper():
                            types += f"field_struct_arr:{struct_name}.{fname}={inner};"
            i += 1
            continue

        # Inside enum body
        if in_enum and indent > 0:
            enum_variants.append(trimmed)
            i += 1
            continue

        # Inside function body
        if in_fn:
            fn_body.append(line)
            i += 1
            continue

        # Top-level statements (go into main or module init)
        # C reserved names that conflict with macros/keywords
        _C_RESERVED = {"EXIT_SUCCESS", "EXIT_FAILURE", "NULL", "EOF", "stdin", "stdout",
                        "stderr", "errno", "SIGINT", "SIGTERM", "SIGKILL", "BUFSIZ",
                        "true", "false", "bool", "FILE"}
        # Check if this is a global constant (val X = literal, should be global)
        if indent == 0 and trimmed.startswith("val ") and " = " in trimmed:
            rest_val = trimmed[4:].strip()
            # Strip trailing comments
            comment_pos = _find_comment_start(rest_val)
            if comment_pos >= 0:
                rest_val = rest_val[:comment_pos].strip()
            eq_pos = rest_val.find(" = ")
            if eq_pos >= 0:
                vname = rest_val[:eq_pos].strip()
                vrhs = rest_val[eq_pos + 3:].strip()
                # Skip C reserved names
                if vname in _C_RESERVED:
                    i += 1
                    continue
                # Integer or float literal → global constant
                if re.match(r'^-?\d+$', vrhs) or re.match(r'^-?\d+\.\d+$', vrhs):
                    global_constants.append(f"const long long {vname} = {vrhs};")
                    i += 1
                    continue
                # String literal → global string constant
                if vrhs.startswith('"') and vrhs.endswith('"') and "{" not in vrhs:
                    global_constants.append(f"const char* {vname} = {vrhs};")
                    types += f"text:{vname};"
                    i += 1
                    continue

        # Track blocks for proper closing
        is_continuation = (trimmed.startswith("elif ") or trimmed == "else:")
        if is_continuation:
            # Close inner blocks that are strictly deeper than current indent
            while main_indent_stack and indent < main_indent_stack[-1]:
                main_indent_stack.pop()
                main_code.append("}")
        else:
            while main_indent_stack and indent <= main_indent_stack[-1]:
                main_indent_stack.pop()
                main_code.append("}")

        result = translate_top_level_statement(trimmed, types)
        if result:
            code = result[0]
            new_types = result[1]
            opens_block = result[2] if len(result) > 2 else False
            types += new_types
            main_code.append(code)

            if opens_block:
                if is_continuation:
                    # elif/else replace the current block, don't push new
                    pass
                else:
                    main_indent_stack.append(indent)

        i += 1

    # Close any remaining main blocks
    while main_indent_stack:
        main_indent_stack.pop()
        main_code.append("}")

    # Finalize any pending function/struct/enum
    if in_fn:
        emit_function(fn_name, fn_sig, fn_orig_line, fn_body, forward_decls, function_bodies, types)
    if in_struct:
        sdef = f"typedef struct {{\n"
        for sf in struct_fields:
            sdef += f"    {sf}\n"
        sdef += f"}} {struct_name};\n"
        struct_defs.append(sdef)
    if in_enum:
        emit_enum(enum_name, enum_variants, enum_defs, types)

    # Build output
    output = []
    output.append("#include <stdio.h>")
    output.append("#include <stdlib.h>")
    output.append("#include <string.h>")
    output.append("#include <stdint.h>")
    output.append('#ifdef _MSC_VER')
    output.append('#define strdup _strdup')
    output.append('#endif')
    output.append("")

    # Read runtime from file
    runtime = read_runtime()
    output.append(runtime)

    # Struct and enum definitions
    for sd in struct_defs:
        output.append(sd)
    for ed in enum_defs:
        output.append(ed)

    # Global constants
    for gc in global_constants:
        output.append(gc)
    if global_constants:
        output.append("")

    # Forward declarations
    for fd in forward_decls:
        output.append(fd)
    output.append("")

    # Function bodies
    for fb in function_bodies:
        output.append(fb)
        output.append("")

    # Main function (skip if user defined their own main)
    has_user_main = any("main(" in fd for fd in forward_decls)
    if not has_user_main and main_code:
        output.append("int main(void) {")
        for mc in main_code:
            output.append(f"    {mc}")
        output.append("    return 0;")
        output.append("}")
        output.append("")
    elif not has_user_main:
        # Empty main
        output.append("int main(void) { return 0; }")
        output.append("")

    return "\n".join(output)


def _extract_param_types(sig_line):
    """Extract parameter types from a function signature for type tracking."""
    paren_pos = sig_line.find("(")
    close_pos = sig_line.find(")")
    if paren_pos < 0 or close_pos < 0:
        return ""
    params_str = sig_line[paren_pos + 1:close_pos].strip()
    if not params_str:
        return ""
    extra_types = ""
    for param in params_str.split(","):
        p = param.strip()
        colon_idx = p.find(":")
        if colon_idx >= 0:
            pname = p[:colon_idx].strip()
            ptype = p[colon_idx + 1:].strip()
            if ptype in ("text", "str", "String"):
                extra_types += f"text:{pname};"
            elif ptype in ("[text]", "[str]"):
                extra_types += f"arr:{pname};"
            elif ptype in ("[i64]", "[int]"):
                extra_types += f"int_arr:{pname};"
            elif ptype == "bool":
                pass  # treat as int
            elif ptype.startswith("[") and ptype.endswith("]"):
                inner = ptype[1:-1].strip()
                if inner and inner[0].isupper():
                    extra_types += f"struct_arr_var:{pname}={inner};"
            elif ptype and ptype[0].isupper():
                extra_types += f"struct_var:{pname}={ptype};"
    return extra_types


def emit_function(name, sig, orig_line, body_lines, forward_decls, function_bodies, types):
    """Emit a translated function."""
    c_body = []
    indent_stack = []
    # Add parameter types to local type registry
    local_types = types + _extract_param_types(orig_line)

    # Find last non-empty body line for implicit return
    last_nonempty_idx = -1
    for idx, line in enumerate(body_lines):
        if line.strip():
            last_nonempty_idx = idx

    in_docstring = False
    for line_idx, line in enumerate(body_lines):
        if not line.strip():
            continue
        indent = get_indent_level(line)
        trimmed = line.strip()

        # Skip docstrings inside functions
        if trimmed.startswith('"""') or trimmed.startswith("'''"):
            if in_docstring:
                in_docstring = False
                continue
            if trimmed.endswith('"""') and len(trimmed) > 3:
                continue  # single-line docstring
            in_docstring = True
            continue
        if in_docstring:
            continue

        # Strip comments
        if trimmed.startswith("#"):
            continue
        comment_pos = _find_comment_start(trimmed)
        if comment_pos > 0:
            trimmed = trimmed[:comment_pos].rstrip()
            if not trimmed:
                continue

        # Close blocks
        is_continuation = (trimmed.startswith("elif ") or trimmed == "else:")
        if is_continuation:
            # Close inner blocks that are strictly deeper than current indent
            # (the elif/else `} else {` handles closing at the current level)
            while indent_stack and indent < indent_stack[-1]:
                indent_stack.pop()
                c_body.append("    " * (len(indent_stack) + 1) + "}")
        else:
            while indent_stack and indent <= indent_stack[-1]:
                indent_stack.pop()
                c_body.append("    " * (len(indent_stack) + 1) + "}")

        # Check if this is the last line and might be an implicit return
        is_last = (line_idx == last_nonempty_idx)
        is_implicit_return = False
        if is_last and indent == 1 and not indent_stack:
            # Last line at base function indent, not inside a block
            # Check if it's already a return or a non-expression statement
            # Use string-aware check for assignment operators
            has_assign = len(_split_top_level_str(trimmed, " = ")) >= 2
            has_plus_assign = len(_split_top_level_str(trimmed, " += ")) >= 2
            has_minus_assign = len(_split_top_level_str(trimmed, " -= ")) >= 2
            if not (trimmed.startswith("return") or trimmed.startswith("if ") or
                    trimmed.startswith("elif ") or trimmed == "else:" or
                    trimmed.startswith("for ") or trimmed.startswith("while ") or
                    trimmed.startswith("val ") or trimmed.startswith("var ") or
                    trimmed.startswith("print ") or has_assign or
                    has_plus_assign or has_minus_assign or
                    trimmed in ("pass", "pass_do_nothing", "pass_dn", "pass_todo",
                                "break", "continue") or
                    trimmed.endswith(";")):
                # Likely an implicit return expression
                is_implicit_return = True

        if is_implicit_return:
            c_expr = translate_expr(trimmed, local_types)
            padding = "    " * (len(indent_stack) + 1)
            c_body.append(f"{padding}return {c_expr};")
        else:
            result = translate_statement(trimmed, local_types, len(indent_stack) + 1)
            if result:
                code = result[0]
                new_types = result[1]
                opens_block = result[2] if len(result) > 2 else False

                if new_types:
                    local_types = local_types + new_types

                padding = "    " * (len(indent_stack) + 1)
                c_body.append(f"{padding}{code}")

                if opens_block and not is_continuation:
                    indent_stack.append(indent)

    # Close remaining blocks
    while indent_stack:
        indent_stack.pop()
        c_body.append("    " * (len(indent_stack) + 1) + "}")

    fn_code = f"{sig} {{\n"
    fn_code += "\n".join(c_body)
    fn_code += "\n}\n"
    function_bodies.append(fn_code)


def translate_statement(trimmed, types, depth=0):
    """Translate a single statement. Returns (code, new_type_entries, opens_block)."""
    # pass / pass_do_nothing / pass_dn / pass_todo
    if trimmed in ("pass", "pass_do_nothing", "pass_dn", "pass_todo"):
        return ("/* pass */", "", False)

    # return
    if trimmed == "return":
        return ("return;", "", False)
    if trimmed.startswith("return "):
        expr = trimmed[7:].strip()
        c_expr = translate_expr(expr, types)
        return (f"return {c_expr};", "", False)

    # break / continue
    if trimmed == "break":
        return ("break;", "", False)
    if trimmed == "continue":
        return ("continue;", "", False)

    # if / elif / else
    # Inline if: "if cond: body_statement" (not just "if cond:")
    if trimmed.startswith("if ") and ": " in trimmed:
        colon_pos = _find_if_colon(trimmed)
        if colon_pos >= 0:
            after_colon = trimmed[colon_pos + 2:].strip()
            if after_colon:
                # This is inline: if cond: statement
                cond = trimmed[3:colon_pos].strip()
                c_cond = translate_condition(cond, types)
                inner = translate_statement(after_colon, types, depth)
                if inner:
                    return (f"if ({c_cond}) {{ {inner[0]} }}", inner[1], False)
                return (f"if ({c_cond}) {{ /* {after_colon} */ }}", "", False)

    if trimmed.startswith("if ") and trimmed.endswith(":"):
        cond = trimmed[3:-1].strip()
        # Handle "if val X = expr:" pattern
        if cond.startswith("val "):
            parts = cond[4:].split("=", 1)
            if len(parts) == 2:
                vname = parts[0].strip()
                vexpr = parts[1].strip()
                c_expr = translate_expr(vexpr, types)
                return (f"{{ const char* {vname} = {c_expr}; if ({vname} != NULL) {{", "", True)
        c_cond = translate_condition(cond, types)
        return (f"if ({c_cond}) {{", "", True)

    if trimmed.startswith("elif ") and trimmed.endswith(":"):
        cond = trimmed[5:-1].strip()
        c_cond = translate_condition(cond, types)
        return (f"}} else if ({c_cond}) {{", "", True)

    if trimmed == "else:":
        return ("} else {", "", True)

    # for loop (also convert range syntax: for x in 0..n: → for x in range(0, n):)
    if trimmed.startswith("for ") and trimmed.endswith(":"):
        # Convert .. range syntax manually (regex can't handle expr..expr with dots)
        trimmed_for = trimmed
        m_range = re.match(r'for (\w+) in (.+):', trimmed)
        if m_range:
            iter_part = m_range.group(2).strip()
            # Find ".." that is not inside parens or strings
            dd_pos = _find_dotdot(iter_part)
            if dd_pos >= 0:
                range_start = iter_part[:dd_pos].strip()
                range_end = iter_part[dd_pos + 2:].strip()
                trimmed_for = f"for {m_range.group(1)} in range({range_start}, {range_end}):"
        return translate_for_statement(trimmed_for, types)

    # while loop
    if trimmed.startswith("while ") and trimmed.endswith(":"):
        cond = trimmed[6:-1].strip()
        c_cond = translate_condition(cond, types)
        return (f"while ({c_cond}) {{", "", True)

    # match statement: match expr:
    if trimmed.startswith("match ") and trimmed.endswith(":"):
        match_expr = trimmed[6:-1].strip()
        c_expr = translate_expr(match_expr, types)
        return (f"{{ long long _match_val = {c_expr}; if (0) {{", "", True)

    # match case: value: / pattern: (inside match block)
    # Handle common match patterns: integer, string, enum variant, _
    if trimmed.endswith(":") and not trimmed.startswith("fn ") and not trimmed.startswith("class "):
        case_body = trimmed[:-1].strip()
        if case_body == "_":
            return ("} else {", "", True)
        if case_body.startswith("Some("):
            # Some(x): pattern — extract binding variable
            inner = case_body[5:-1].strip()
            return (f"}} else if (_match_val != 0) {{ long long {inner} = _match_val;", "", True)
        if case_body == "nil" or case_body == "None":
            return ("} else if (_match_val == 0) {", "", True)
        # Integer literal
        if re.match(r'^-?\d+$', case_body):
            return (f"}} else if (_match_val == {case_body}) {{", "", True)
        # String literal
        if case_body.startswith('"'):
            c_case = translate_expr(case_body, types)
            return (f"}} else if (strcmp(_match_val, {c_case}) == 0) {{", "", True)
        # Enum variant or identifier
        c_case = translate_expr(case_body, types)
        return (f"}} else if (_match_val == {c_case}) {{", "", True)

    # print
    if trimmed.startswith("print ") or trimmed == "print":
        return translate_print_statement(trimmed, types)

    # val/var declaration
    if trimmed.startswith("val ") or trimmed.startswith("var "):
        return translate_var_decl(trimmed, types)

    # Walrus operator: name := expr
    if " := " in trimmed:
        parts = trimmed.split(" := ", 1)
        name = parts[0].strip()
        rhs = parts[1].strip()
        c_rhs = translate_expr(rhs, types)
        new_types = ""
        if rhs.startswith('"') or is_fn_returning_text(rhs.split("(")[0].strip() if "(" in rhs else "", types):
            new_types = f"text:{name};"
            return (f"const char* {name} = {c_rhs};", new_types, False)
        return (f"long long {name} = {c_rhs};", new_types, False)

    # Assignment: name = expr (use string-aware check)
    _eq_parts = _split_top_level_str(trimmed, " = ")
    if len(_eq_parts) >= 2 and not trimmed.startswith("if "):
        lhs = _eq_parts[0].strip()
        rhs = " = ".join(_eq_parts[1:]).strip()
        c_rhs = translate_expr(rhs, types)
        # Translate LHS for self.field → self->field
        c_lhs = lhs
        if lhs.startswith("self."):
            c_lhs = "self->" + lhs[5:]
        return (f"{c_lhs} = {c_rhs};", "", False)

    # Compound assignment (use string-aware check)
    for op in [" += ", " -= ", " *= ", " /= "]:
        _cop_parts = _split_top_level_str(trimmed, op)
        if len(_cop_parts) >= 2:
            lhs = _cop_parts[0].strip()
            rhs = _cop_parts[1].strip()
            c_rhs = translate_expr(rhs, types)
            if op == " += " and (is_text_var(lhs, types) or rhs.startswith('"')):
                return (f"{lhs} = simple_str_concat({lhs}, {c_rhs});", "", False)
            return (f"{lhs} {op.strip()} {c_rhs};", "", False)

    # Method call as statement: obj.method(args)
    if "." in trimmed and "(" in trimmed:
        c_expr = translate_method_call(trimmed, types)
        return (f"{c_expr};", "", False)

    # Function call as statement
    if "(" in trimmed:
        c_expr = translate_expr(trimmed, types)
        return (f"{c_expr};", "", False)

    # Fallback
    return (f"/* unsupported: {trimmed} */", "", False)


def translate_for_statement(trimmed, types):
    """Translate a for loop."""
    # Parse "for VAR in EXPR:" using proper parsing
    m_for = re.match(r'for (\w+) in (.+):', trimmed)
    if not m_for:
        return (f"/* unsupported for: {trimmed} */", "", False)

    loop_var = m_for.group(1)
    iter_expr = m_for.group(2).strip()

    # for var in range(start, end):
    if iter_expr.startswith("range(") and iter_expr.endswith(")"):
        range_inner = iter_expr[6:-1].strip()
        range_parts = split_top_level(range_inner, ",")
        if len(range_parts) >= 2:
            start = translate_expr(range_parts[0].strip(), types)
            end = translate_expr(range_parts[1].strip(), types)
            return (f"for (long long {loop_var} = {start}; {loop_var} < {end}; {loop_var}++) {{", "", True)
        elif len(range_parts) == 1:
            end = translate_expr(range_parts[0].strip(), types)
            return (f"for (long long {loop_var} = 0; {loop_var} < {end}; {loop_var}++) {{", "", True)

    # for var in array:
    m = m_for
    if m:
        loop_var = m.group(1)
        iterable = m.group(2).strip()
        c_iter = translate_expr(iterable, types)
        if is_string_array_var(iterable, types):
            idx_var = f"_idx_{loop_var}"
            return (
                f"for (long long {idx_var} = 0; {idx_var} < {c_iter}.len; {idx_var}++) {{ const char* {loop_var} = {c_iter}.items[{idx_var}];",
                f"text:{loop_var};", True
            )
        if is_int_array_var(iterable, types):
            idx_var = f"_idx_{loop_var}"
            return (
                f"for (long long {idx_var} = 0; {idx_var} < {c_iter}.len; {idx_var}++) {{ long long {loop_var} = {c_iter}.items[{idx_var}];",
                "", True
            )
        # Default: assume string array
        idx_var = f"_idx_{loop_var}"
        return (
            f"for (long long {idx_var} = 0; {idx_var} < {c_iter}.len; {idx_var}++) {{ const char* {loop_var} = {c_iter}.items[{idx_var}];",
            f"text:{loop_var};", True
        )

    return (f"/* unsupported for: {trimmed} */", "", False)


def translate_print_statement(trimmed, types):
    """Translate print statement."""
    if trimmed == "print":
        return ('puts("");', "", False)

    arg = trimmed[6:].strip()

    # print "string with {interpolation}" - but only if it's a SINGLE string literal
    if arg.startswith('"'):
        close_quote = _find_close_quote(arg, 0)
        if close_quote >= 0 and close_quote == len(arg) - 1:
            # Single string literal
            inner = arg[1:-1]
            if "{" not in inner:
                return (f'puts("{inner}");', "", False)
            # Build printf
            return translate_interpolated_print(inner, types)

    # print variable
    c_arg = translate_expr(arg, types)
    if is_text_expression(arg, types):
        return (f'puts({c_arg});', "", False)
    return (f'printf("%lld\\n", (long long){c_arg});', "", False)


def translate_interpolated_print(inner, types):
    """Translate interpolated print string to printf."""
    fmt_parts = []
    args = []
    i = 0
    while i < len(inner):
        if inner[i] == '\\' and i + 1 < len(inner):
            fmt_parts.append(inner[i:i+2])
            i += 2
            continue
        # Escaped braces: {{ → literal {, }} → literal }
        if inner[i] == '{' and i + 1 < len(inner) and inner[i + 1] == '{':
            fmt_parts.append('{')
            i += 2
            continue
        if inner[i] == '}' and i + 1 < len(inner) and inner[i + 1] == '}':
            fmt_parts.append('}')
            i += 2
            continue
        if inner[i] == '{':
            j = i + 1
            depth = 0
            while j < len(inner):
                if inner[j] == '}' and depth == 0:
                    break
                if inner[j] == '{':
                    depth += 1
                elif inner[j] == '}':
                    depth -= 1
                j += 1
            if j < len(inner):
                raw_expr = inner[i + 1:j]
                c_expr = translate_expr(raw_expr, types)
                if is_text_expression(raw_expr, types):
                    fmt_parts.append("%s")
                    args.append(c_expr)
                else:
                    fmt_parts.append("%lld")
                    args.append(f"(long long){c_expr}")
                i = j + 1
                continue
        fmt_parts.append(inner[i])
        i += 1

    fmt_str = ''.join(fmt_parts)
    if args:
        args_str = ", ".join(args)
        return (f'printf("{fmt_str}\\n", {args_str});', "", False)
    return (f'puts("{fmt_str}");', "", False)


def translate_var_decl(trimmed, types):
    """Translate val/var declaration."""
    is_val = trimmed.startswith("val ")
    rest = trimmed[4:].strip()

    # Type annotation: var name: Type = expr
    type_match = re.match(r'(\w+)\s*:\s*([^=]+?)\s*=\s*(.+)', rest)
    if type_match:
        name = type_match.group(1)
        type_hint = type_match.group(2).strip()
        rhs = type_match.group(3).strip()
        c_type = simple_type_to_c(type_hint)
        new_types = ""

        if type_hint in ("text", "str", "String"):
            new_types = f"text:{name};"
        elif type_hint in ("[text]", "[str]"):
            new_types = f"arr:{name};"
        elif type_hint in ("[i64]", "[int]", "[bool]"):
            new_types = f"int_arr:{name};"
        elif type_hint.startswith("[") and type_hint.endswith("]"):
            inner = type_hint[1:-1].strip()
            if inner and inner[0].isupper():
                new_types = f"struct_arr_var:{name}={inner};"
        elif type_hint and type_hint[0].isupper():
            new_types = f"struct_var:{name}={type_hint};"

        # Override empty array init based on type
        if rhs == "[]":
            if type_hint in ("[i64]", "[int]", "[bool]"):
                return (f"{c_type} {name} = simple_new_int_array();", new_types, False)
            elif type_hint in ("[text]", "[str]"):
                return (f"{c_type} {name} = simple_new_string_array();", new_types, False)
            elif type_hint.startswith("[") and type_hint.endswith("]"):
                inner = type_hint[1:-1].strip()
                if inner and inner[0].isupper():
                    return (f"SimpleStructArray {name} = simple_new_struct_array();", new_types, False)

        c_rhs = translate_expr(rhs, types)
        return (f"{c_type} {name} = {c_rhs};", new_types, False)

    # Simple: var name = expr
    eq_pos = rest.find(" = ")
    if eq_pos < 0:
        eq_pos = rest.find("=")
        if eq_pos >= 0:
            name = rest[:eq_pos].strip()
            rhs = rest[eq_pos + 1:].strip()
        else:
            # Declaration without init
            name = rest.strip()
            return (f"long long {name} = 0;", "", False)
    else:
        name = rest[:eq_pos].strip()
        rhs = rest[eq_pos + 3:].strip()

    # Type annotation without init
    if ":" in name:
        colon_pos = name.find(":")
        var_name = name[:colon_pos].strip()
        type_hint = name[colon_pos + 1:].strip()
        c_type = simple_type_to_c(type_hint)
        c_rhs = translate_expr(rhs, types)
        new_types = ""
        if type_hint in ("text", "str", "String"):
            new_types = f"text:{var_name};"
        elif type_hint in ("[text]", "[str]"):
            new_types = f"arr:{var_name};"
        elif type_hint in ("[i64]", "[int]"):
            new_types = f"int_arr:{var_name};"
        return (f"{c_type} {var_name} = {c_rhs};", new_types, False)

    c_rhs = translate_expr(rhs, types)
    new_types = ""

    # Infer type from RHS
    if rhs.startswith('"'):
        new_types = f"text:{name};"
        qual = "const char*" if is_val else "const char*"
        return (f"{qual} {name} = {c_rhs};", new_types, False)
    if rhs == "[]":
        new_types = f"arr:{name};"
        return (f"SimpleStringArray {name} = simple_new_string_array();", new_types, False)
    if rhs.startswith("[") and rhs.endswith("]"):
        # Array literal
        inner_content = rhs[1:-1].strip()
        if inner_content.startswith('"') or inner_content.startswith("'"):
            new_types = f"arr:{name};"
            items = split_top_level(inner_content, ",")
            init_code = f"SimpleStringArray {name} = simple_new_string_array();"
            for item in items:
                item = item.strip()
                if item:
                    c_item = translate_expr(item, types)
                    init_code += f" simple_string_push(&{name}, {c_item});"
            return (init_code, new_types, False)
        elif inner_content:
            new_types = f"int_arr:{name};"
            items = split_top_level(inner_content, ",")
            init_code = f"SimpleIntArray {name} = simple_new_int_array();"
            for item in items:
                item = item.strip()
                if item:
                    c_item = translate_expr(item, types)
                    init_code += f" simple_int_push(&{name}, {c_item});"
            return (init_code, new_types, False)
        else:
            new_types = f"arr:{name};"
            return (f"SimpleStringArray {name} = simple_new_string_array();", new_types, False)
    if "(" in rhs:
        fn_name_call = rhs[:rhs.find("(")].strip()
        # Struct constructor: val p = Point(x: 3, y: 4)
        if is_known_struct(fn_name_call, types):
            new_types = f"struct_var:{name}={fn_name_call};"
            return (f"{fn_name_call} {name} = {c_rhs};", new_types, False)
        if is_fn_returning_text(fn_name_call, types):
            new_types = f"text:{name};"
            return (f"const char* {name} = {c_rhs};", new_types, False)
        struct_ret = is_fn_returning_struct(fn_name_call, types)
        if struct_ret:
            new_types = f"struct_var:{name}={struct_ret};"
            return (f"{struct_ret} {name} = {c_rhs};", new_types, False)
        if is_fn_returning_str_arr(fn_name_call, types):
            new_types = f"arr:{name};"
            return (f"SimpleStringArray {name} = {c_rhs};", new_types, False)
        if is_fn_returning_int_arr(fn_name_call, types):
            new_types = f"int_arr:{name};"
            return (f"SimpleIntArray {name} = {c_rhs};", new_types, False)
    # Method call return type inference
    if "." in rhs and "(" in rhs:
        dot_pos = rhs.find(".")
        method_start = rhs[dot_pos + 1:]
        if method_start.startswith("split("):
            # Check if there's a .len() or .len after split — that returns a number
            if ".len()" in rhs or (rhs.endswith(".len") and ".split(" in rhs):
                return (f"long long {name} = {c_rhs};", new_types, False)
            new_types = f"arr:{name};"
            return (f"SimpleStringArray {name} = {c_rhs};", new_types, False)
        if (method_start.startswith("trim(") or method_start.startswith("replace(") or
            method_start.startswith("substring(") or method_start.startswith("slice(") or
            method_start.startswith("to_upper(") or method_start.startswith("to_lower(") or
            method_start.startswith("char_at(")):
            new_types = f"text:{name};"
            return (f"const char* {name} = {c_rhs};", new_types, False)
        if method_start.startswith("join("):
            new_types = f"text:{name};"
            return (f"const char* {name} = {c_rhs};", new_types, False)
    # String operations
    if is_text_var(rhs, types) or " + " in rhs:
        # Check if string concatenation
        if rhs.startswith('"') or any(is_text_var(p.strip(), types) for p in rhs.split(" + ")):
            new_types = f"text:{name};"
            return (f"const char* {name} = {c_rhs};", new_types, False)

    return (f"long long {name} = {c_rhs};", new_types, False)


def translate_top_level_statement(trimmed, types):
    """Translate a top-level statement (goes in main)."""
    return translate_statement(trimmed, types)


def emit_enum(enum_name, variants, enum_defs, types):
    """Emit an enum definition as a C tagged union."""
    edef = f"typedef struct {{\n    int tag;\n}} {enum_name};\n"
    tag_defs = ""
    constructors = ""
    tag_idx = 0
    for v in variants:
        v = v.strip()
        if not v or v.startswith("#"):
            continue
        if "(" in v:
            vname = v[:v.find("(")].strip()
        else:
            vname = v.rstrip(":")
        tag_defs += f"#define {enum_name}_TAG_{vname} {tag_idx}\n"
        types += f"enum_variant:{enum_name}.{vname};"
        tag_idx += 1
    enum_defs.append(edef + tag_defs + constructors)


def read_runtime():
    """Read the C runtime from file."""
    if os.path.exists(RUNTIME_PATH):
        with open(RUNTIME_PATH) as f:
            return f.read()
    # Minimal fallback
    return """
// === Minimal Simple Runtime ===
static long long simple_strlen(const char* s) { return s ? (long long)strlen(s) : 0; }
static int simple_contains(const char* s, const char* n) { return s && n && strstr(s, n) != NULL; }
static int simple_starts_with(const char* s, const char* p) { return s && p && strncmp(s, p, strlen(p)) == 0; }
static int simple_ends_with(const char* s, const char* x) { long sl = strlen(s), xl = strlen(x); return xl <= sl && strcmp(s+sl-xl, x) == 0; }
static long long simple_index_of(const char* s, const char* n) { const char* f = strstr(s, n); return f ? (long long)(f-s) : -1; }
"""


# ============================================================
# Main
# ============================================================

def main():
    args = sys.argv[1:]

    if not args or args[0] in ('-h', '--help'):
        print(__doc__)
        sys.exit(0)

    if args[0] == '--multi':
        files = []
        output = None
        i = 1
        while i < len(args):
            if args[i] == '--out' and i + 1 < len(args):
                output = args[i + 1]
                i += 2
            else:
                files.append(args[i])
                i += 1
        source_parts = []
        for f in files:
            with open(f, 'r') as fh:
                source_parts.append(fh.read())
        source_text = '\n'.join(source_parts)
    else:
        input_file = args[0]
        output = args[1] if len(args) > 1 else None
        with open(input_file, 'r') as f:
            source_text = f.read()

    c_code = generate_c_code(source_text)

    if output:
        with open(output, 'w') as f:
            f.write(c_code)
        print(f"Generated {output} ({len(c_code)} bytes)", file=sys.stderr)
    else:
        print(c_code)


if __name__ == '__main__':
    main()
