#include "runtime_value.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

typedef struct {
    char fill;
    char align;      /* '<', '>', '^', '=' or 0 */
    char sign;       /* '+', '-', ' ' or 0 */
    int  alt_form;
    int  zero_pad;
    int  width;      /* -1 = none */
    char grouping;   /* ',' or '_' or 0 */
    int  precision;  /* -1 = none */
    char type_code;  /* 'f','d','e','x','o','b','s','%' or 0 */
} FormatSpec;

static FormatSpec parse_format_spec(const char *spec, int spec_len) {
    FormatSpec fs = { .fill = ' ', .width = -1, .precision = -1 };
    int pos = 0;

    /* [fill]align */
    if (spec_len >= 2 && (spec[1] == '<' || spec[1] == '>' || spec[1] == '^' || spec[1] == '=')) {
        fs.fill = spec[0];
        fs.align = spec[1];
        pos = 2;
    } else if (spec_len >= 1 && (spec[0] == '<' || spec[0] == '>' || spec[0] == '^' || spec[0] == '=')) {
        fs.align = spec[0];
        pos = 1;
    }

    /* sign */
    if (pos < spec_len && (spec[pos] == '+' || spec[pos] == '-' || spec[pos] == ' ')) {
        fs.sign = spec[pos++];
    }

    /* alt form '#' */
    if (pos < spec_len && spec[pos] == '#') { fs.alt_form = 1; pos++; }

    /* zero pad '0' */
    if (pos < spec_len && spec[pos] == '0') { fs.zero_pad = 1; pos++; }

    /* width (digits) */
    if (pos < spec_len && spec[pos] >= '0' && spec[pos] <= '9') {
        fs.width = 0;
        while (pos < spec_len && spec[pos] >= '0' && spec[pos] <= '9') {
            fs.width = fs.width * 10 + (spec[pos++] - '0');
        }
    }

    /* grouping */
    if (pos < spec_len && (spec[pos] == ',' || spec[pos] == '_')) {
        fs.grouping = spec[pos++];
    }

    /* .precision */
    if (pos < spec_len && spec[pos] == '.') {
        pos++;
        fs.precision = 0;
        while (pos < spec_len && spec[pos] >= '0' && spec[pos] <= '9') {
            fs.precision = fs.precision * 10 + (spec[pos++] - '0');
        }
    }

    /* type code */
    if (pos < spec_len) { fs.type_code = spec[pos]; }

    return fs;
}

static int apply_alignment(char *out, int out_cap, const char *s, int slen, const FormatSpec *fs) {
    int width = fs->width;
    if (width <= 0 || slen >= width) {
        if (slen > out_cap) slen = out_cap;
        memcpy(out, s, slen);
        return slen;
    }

    int padding = width - slen;
    char fill = (fs->zero_pad && fs->align == 0) ? '0' : fs->fill;
    char align = fs->align;
    if (align == 0) align = fs->zero_pad ? '>' : '<';

    int o = 0;
    if (align == '>') {
        /* zero-pad after sign */
        if (fill == '0' && slen > 0 && (s[0] == '+' || s[0] == '-' || s[0] == ' ')) {
            if (o < out_cap) out[o++] = s[0];
            for (int i = 0; i < padding && o < out_cap; i++) out[o++] = fill;
            for (int i = 1; i < slen && o < out_cap; i++) out[o++] = s[i];
        } else {
            for (int i = 0; i < padding && o < out_cap; i++) out[o++] = fill;
            for (int i = 0; i < slen && o < out_cap; i++) out[o++] = s[i];
        }
    } else if (align == '<') {
        for (int i = 0; i < slen && o < out_cap; i++) out[o++] = s[i];
        for (int i = 0; i < padding && o < out_cap; i++) out[o++] = fill;
    } else if (align == '^') {
        int left = padding / 2, right = padding - left;
        for (int i = 0; i < left && o < out_cap; i++) out[o++] = fill;
        for (int i = 0; i < slen && o < out_cap; i++) out[o++] = s[i];
        for (int i = 0; i < right && o < out_cap; i++) out[o++] = fill;
    } else if (align == '=') {
        if (slen > 0 && (s[0] == '+' || s[0] == '-' || s[0] == ' ')) {
            if (o < out_cap) out[o++] = s[0];
            for (int i = 0; i < padding && o < out_cap; i++) out[o++] = fill;
            for (int i = 1; i < slen && o < out_cap; i++) out[o++] = s[i];
        } else {
            for (int i = 0; i < padding && o < out_cap; i++) out[o++] = fill;
            for (int i = 0; i < slen && o < out_cap; i++) out[o++] = s[i];
        }
    }
    return o;
}

static int format_sign(char *buf, int cap, const char *num, int nlen, int is_positive, const FormatSpec *fs) {
    int o = 0;
    if (!is_positive) {
        if (o < cap) buf[o++] = '-';
    } else if (fs->sign == '+') {
        if (o < cap) buf[o++] = '+';
    } else if (fs->sign == ' ') {
        if (o < cap) buf[o++] = ' ';
    }
    for (int i = 0; i < nlen && o < cap; i++) buf[o++] = num[i];
    return o;
}

int64_t __c_rt_value_format_string(RuntimeValue v, const uint8_t *fmt_ptr, uint64_t fmt_len,
                                    uint8_t *out, uint64_t out_cap) {
    FormatSpec fs = parse_format_spec((const char *)fmt_ptr, (int)fmt_len);
    char raw[256];
    int rlen = 0;

    /* Extract numeric value */
    double fval = 0.0;
    int64_t ival = 0;
    int is_int = rv_is_int(v), is_float = rv_is_float(v);
    if (is_int) ival = rv_to_int(v);
    if (is_float) fval = rv_to_float(v);

    switch (fs.type_code) {
    case 'f': case 'F': {
        double f = is_float ? fval : (is_int ? (double)ival : 0.0);
        int prec = fs.precision >= 0 ? fs.precision : 6;
        char tmp[128];
        int tlen = snprintf(tmp, sizeof(tmp), "%.*f", prec, fabs(f));
        rlen = format_sign(raw, sizeof(raw), tmp, tlen, f >= 0.0, &fs);
        break;
    }
    case 'e': case 'E': {
        double f = is_float ? fval : (is_int ? (double)ival : 0.0);
        int prec = fs.precision >= 0 ? fs.precision : 6;
        rlen = snprintf(raw, sizeof(raw), fs.type_code == 'E' ? "%.*E" : "%.*e", prec, f);
        break;
    }
    case 'd': {
        int64_t i = is_int ? ival : (is_float ? (int64_t)fval : 0);
        char tmp[64];
        int tlen = snprintf(tmp, sizeof(tmp), "%lld", (long long)(i < 0 ? -i : i));
        rlen = format_sign(raw, sizeof(raw), tmp, tlen, i >= 0, &fs);
        break;
    }
    case 'x': case 'X': {
        int64_t i = is_int ? ival : 0;
        if (fs.alt_form)
            rlen = snprintf(raw, sizeof(raw), fs.type_code == 'X' ? "0X%llX" : "0x%llx", (unsigned long long)i);
        else
            rlen = snprintf(raw, sizeof(raw), fs.type_code == 'X' ? "%llX" : "%llx", (unsigned long long)i);
        break;
    }
    case 'o': {
        int64_t i = is_int ? ival : 0;
        rlen = snprintf(raw, sizeof(raw), fs.alt_form ? "0o%llo" : "%llo", (unsigned long long)i);
        break;
    }
    case 'b': {
        uint64_t u = (uint64_t)(is_int ? ival : 0);
        int o = 0;
        if (fs.alt_form) { raw[o++] = '0'; raw[o++] = 'b'; }
        if (u == 0) { raw[o++] = '0'; }
        else {
            char tmp[64]; int t = 0;
            while (u) { tmp[t++] = '0' + (u & 1); u >>= 1; }
            for (int i = t - 1; i >= 0; i--) raw[o++] = tmp[i];
        }
        rlen = o;
        break;
    }
    case '%': {
        double f = is_float ? fval : (is_int ? (double)ival : 0.0);
        int prec = fs.precision >= 0 ? fs.precision : 6;
        rlen = snprintf(raw, sizeof(raw), "%.*f%%", prec, f * 100.0);
        break;
    }
    default: { /* 's' or default: convert to display string */
        if (rv_tag(v) == TAG_INT) {
            rlen = snprintf(raw, sizeof(raw), "%lld", (long long)rv_to_int(v));
        } else if (rv_tag(v) == TAG_FLOAT) {
            rlen = snprintf(raw, sizeof(raw), "%g", rv_to_float(v));
        } else if (rv_tag(v) == TAG_SPECIAL) {
            uint64_t p = rv_payload(v);
            if (p == SPECIAL_TRUE) { memcpy(raw, "true", 4); rlen = 4; }
            else if (p == SPECIAL_FALSE) { memcpy(raw, "false", 5); rlen = 5; }
            else if (p == SPECIAL_NIL) { memcpy(raw, "nil", 3); rlen = 3; }
            else { rlen = snprintf(raw, sizeof(raw), "<special:%llu>", (unsigned long long)p); }
        } else if (rv_tag(v) == TAG_HEAP) {
            HeapHeader *h = (HeapHeader *)rv_as_heap_ptr(v);
            if (h && (uintptr_t)h >= MIN_HEAP_ADDR && h->object_type == HEAP_TYPE_STRING) {
                RuntimeString *s = (RuntimeString *)h;
                const uint8_t *data = (const uint8_t *)(s + 1);
                int slen = (int)s->len;
                if (fs.precision >= 0 && slen > fs.precision) slen = fs.precision;
                int result = apply_alignment((char *)out, (int)out_cap, (const char *)data, slen, &fs);
                return (int64_t)result;
            }
            rlen = snprintf(raw, sizeof(raw), "<heap@%p>", (void *)h);
        } else {
            rlen = snprintf(raw, sizeof(raw), "<value:0x%llx>", (unsigned long long)v);
        }
        if (fs.precision >= 0 && fs.type_code == 's' && rlen > fs.precision) rlen = fs.precision;
        break;
    }
    }

    int result = apply_alignment((char *)out, (int)out_cap, raw, rlen, &fs);
    return (int64_t)result;
}
