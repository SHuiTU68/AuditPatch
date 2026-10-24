#include <android/log.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <pthread.h>
#include "dobby.h"

#define LOG_TAG "auditpatch"
#define LOGI(...) __android_log_print(ANDROID_LOG_INFO, LOG_TAG, __VA_ARGS__)
#define LOGE(...) __android_log_print(ANDROID_LOG_ERROR, LOG_TAG, __VA_ARGS__)

#define ENC_KEY 0x37

/* Compile-time policy for the sandbox carrier domains (app_zygote / isolated).
   0 = install the hook everywhere (nothing containing a sensitive context can
       reach logcat from any domain);
   1 = v0.4 behaviour, skip those domains entirely (lowest possible overhead,
       but real context strings may escape there). */
#ifndef AP_SKIP_CARRIER
#define AP_SKIP_CARRIER 0
#endif

#define RULE_N 5
#define FIELD_MAX 48

static const unsigned char enc_src0[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x44,0x42,0x0d,0x44,0x07};
static const unsigned char enc_src1[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x5a,0x56,0x50,0x5e,0x44,0x5c,0x0d,0x44,0x07};
static const unsigned char enc_src2[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x5c,0x44,0x42,0x0d,0x44,0x07};
static const unsigned char enc_src3[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x58,0x55,0x5d,0x52,0x54,0x43,0x68,0x45,0x0d,0x5c,0x44,0x42,0x68,0x51,0x5e,0x5b,0x52,0x0d,0x44,0x07};
static const unsigned char enc_src4[] = {0x44,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x5c,0x44,0x42,0x0d,0x44,0x07};

static const unsigned char enc_dstA[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x47,0x45,0x5e,0x41,0x68,0x56,0x47,0x47,0x0d,0x44,0x07,0x0d,0x54,0x02,0x06,0x05,0x1b,0x54,0x00,0x01,0x0f};
static const unsigned char enc_dstB[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x58,0x55,0x5d,0x52,0x54,0x43,0x68,0x45,0x0d,0x56,0x47,0x47,0x68,0x53,0x56,0x43,0x56,0x68,0x51,0x5e,0x5b,0x52,0x0d,0x44,0x07};
static const unsigned char enc_dstC[] = {0x44,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x42,0x59,0x43,0x45,0x42,0x44,0x43,0x52,0x53,0x68,0x56,0x47,0x47,0x0d,0x44,0x07};

static const unsigned char enc_avc[] = {0x56,0x41,0x54,0x0d};
static const unsigned char enc_audit[] = {0x56,0x42,0x53,0x5e,0x43,0x1f};
static const unsigned char enc_ctx[] = {0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a};
static const unsigned char enc_zygote[] = {0x56,0x47,0x47,0x68,0x4d,0x4e,0x50,0x58,0x43,0x52};
static const unsigned char enc_iso[] = {0x5e,0x44,0x58,0x5b,0x56,0x43,0x52,0x53};
static const unsigned char enc_sym[] = {0x41,0x56,0x44,0x47,0x45,0x5e,0x59,0x43,0x51};
static const unsigned char enc_lib[] = {0x5b,0x5e,0x55,0x54,0x19,0x44,0x58};

typedef struct {
    const char *src;
    size_t slen;
    const char *dst;
    size_t dlen;
} rule_t;

static rule_t g_rules[RULE_N];

static char g_src_buf[RULE_N][FIELD_MAX];
static char g_dst_buf[3][FIELD_MAX];

static char g_avc[8];
static char g_audit[8];
static char g_ctx[16];
static char g_zygote[16];
static char g_iso[16];

static int (*old_vasprintf)(char **strp, const char *fmt, va_list ap) = NULL;

static bool g_ready = false;
/* 1 = this process sits in a sandbox carrier domain. Only consulted when
   AP_SKIP_CARRIER is 1; kept either way for a single diagnostic line. */
static int g_carrier = 0;

static void deobf(char *dst, const unsigned char *src, size_t len) {
    size_t i;
    for (i = 0; i < len; ++i) {
        dst[i] = (char)(src[i] ^ ENC_KEY);
    }
    dst[len] = '\0';
}

/* Bounded substring search, avoids relying on memmem visibility. */
static const char *find_sub(const char *h, size_t hn, const char *nd, size_t nn) {
    if (nn == 0 || hn < nn) {
        return NULL;
    }
    const char *p = h;
    const char *last = h + hn - nn;
    while (p <= last) {
        const char *hit = (const char *) memchr(p, nd[0], (size_t)(last - p + 1));
        if (hit == NULL) {
            return NULL;
        }
        if (memcmp(hit, nd, nn) == 0) {
            return hit;
        }
        p = hit + 1;
    }
    return NULL;
}

static bool in_skip_domain(void) {
    FILE *f = fopen("/proc/self/attr/current", "r");
    if (f == NULL) {
        return false;
    }
    char buf[256];
    size_t got = fread(buf, 1, sizeof(buf) - 1, f);
    fclose(f);
    if (got == 0) {
        return false;
    }
    buf[got] = '\0';
    if (find_sub(buf, got, g_zygote, strlen(g_zygote)) != NULL) {
        return true;
    }
    if (find_sub(buf, got, g_iso, strlen(g_iso)) != NULL) {
        return true;
    }
    return false;
}

/* Gate: only payloads that can carry a context key are worth scanning.
   Every rule below contains "context=", so a single probe covers them all. */
static inline bool gate_audit(const char *s, size_t n) {
    if (n >= 4 && memcmp(s, g_avc, 4) == 0) {
        return true;
    }
    if (n >= 6 && memcmp(s, g_audit, 6) == 0) {
        return true;
    }
    if (n >= 8 && find_sub(s, n, g_ctx, 8) != NULL) {
        return true;
    }
    return false;
}

/* One scan does double duty: with out == NULL it measures the exact output
   length, with out != NULL it fills it. Quotes are honoured so that literal
   arguments are never rewritten. */
static size_t transform(const char *s, size_t n, char *out) {
    size_t i = 0;
    size_t o = 0;
    bool in_quote = false;

    while (i < n) {
        char c = s[i];
        if (c == '"') {
            in_quote = !in_quote;
            if (out != NULL) {
                out[o] = c;
            }
            ++o;
            ++i;
            continue;
        }
        /* Cheap shape test before the rule table: every rule is
           {t,s} + "context=" + ..., so probe 'c' and '=' at fixed offsets.
           Uses the (obfuscated) g_ctx bytes, no plaintext literals. */
        if (!in_quote && (c == 't' || c == 's') && (n - i) >= 10 &&
            s[i + 1] == g_ctx[0] && s[i + 8] == g_ctx[7]) {
            size_t rem = n - i;
            int k;
            for (k = 0; k < RULE_N; ++k) {
                size_t sl = g_rules[k].slen;
                if (rem >= sl && memcmp(s + i, g_rules[k].src, sl) == 0) {
                    if (out != NULL) {
                        memcpy(out + o, g_rules[k].dst, g_rules[k].dlen);
                    }
                    o += g_rules[k].dlen;
                    i += sl;
                    break;
                }
            }
            if (k < RULE_N) {
                continue;
            }
        }
        if (out != NULL) {
            out[o] = c;
        }
        ++o;
        ++i;
    }
    return o;
}

static int my_vasprintf(char **strp, const char *fmt, va_list ap) {
    int result = old_vasprintf(strp, fmt, ap);
    if (result <= 0 || *strp == NULL || !g_ready) {
        return result;
    }

#if AP_SKIP_CARRIER
    if (g_carrier) {
        return result;
    }
#endif

    const char *s = *strp;
    size_t n = (size_t) result;

    if (!gate_audit(s, n)) {
        return result;
    }

    /* Pass 1: measure. Zero allocation unless a rule actually fires. */
    size_t need = transform(s, n, NULL);
    if (need == n) {
        return result;
    }

    char *out = (char *) malloc(need + 1);
    if (out == NULL) {
        /* OOM: leave *strp untouched so the caller keeps valid ownership. */
        return result;
    }

    /* Pass 2: build with the exact measured size. */
    size_t o = transform(s, n, out);
    out[o] = '\0';

    free(*strp);
    *strp = out;
    return (int) o;
}

/* Fork children must judge their own domain: a carrier parent can fork into
   app_zygote, and the parent's verdict does not carry over. */
static void on_fork_child(void) {
    if (g_ready) {
        g_carrier = in_skip_domain() ? 1 : 0;
    }
}

__attribute__((constructor))
static void init(void) {
    deobf(g_src_buf[0], enc_src0, sizeof(enc_src0));
    deobf(g_src_buf[1], enc_src1, sizeof(enc_src1));
    deobf(g_src_buf[2], enc_src2, sizeof(enc_src2));
    deobf(g_src_buf[3], enc_src3, sizeof(enc_src3));
    deobf(g_src_buf[4], enc_src4, sizeof(enc_src4));

    deobf(g_dst_buf[0], enc_dstA, sizeof(enc_dstA));
    deobf(g_dst_buf[1], enc_dstB, sizeof(enc_dstB));
    deobf(g_dst_buf[2], enc_dstC, sizeof(enc_dstC));

    deobf(g_avc, enc_avc, sizeof(enc_avc));
    deobf(g_audit, enc_audit, sizeof(enc_audit));
    deobf(g_ctx, enc_ctx, sizeof(enc_ctx));
    deobf(g_zygote, enc_zygote, sizeof(enc_zygote));
    deobf(g_iso, enc_iso, sizeof(enc_iso));

    char sym[32];
    char lib[16];
    deobf(sym, enc_sym, sizeof(enc_sym));
    deobf(lib, enc_lib, sizeof(enc_lib));

    int k;
    for (k = 0; k < RULE_N; ++k) {
        g_rules[k].src = g_src_buf[k];
        g_rules[k].slen = strlen(g_src_buf[k]);
        g_rules[k].dst = g_dst_buf[0];
        g_rules[k].dlen = strlen(g_dst_buf[0]);
    }
    /* File contexts keep a file type so the rewritten label stays plausible. */
    g_rules[3].dst = g_dst_buf[1];
    g_rules[3].dlen = strlen(g_dst_buf[1]);
    /* scontext is the sender side, so it gets a plain app-domain label. */
    g_rules[4].dst = g_dst_buf[2];
    g_rules[4].dlen = strlen(g_dst_buf[2]);

    g_carrier = in_skip_domain() ? 1 : 0;
    pthread_atfork(NULL, NULL, on_fork_child);

#if AP_SKIP_CARRIER
    if (g_carrier) {
        LOGI("Skipping sandbox carrier domain");
        return;
    }
#endif

    g_ready = true;

    void *addr = DobbySymbolResolver(lib, sym);
    if (addr == NULL) {
        LOGE("Failed to resolve symbol");
        return;
    }

    if (DobbyHook(addr, (void *) my_vasprintf, (void **) &old_vasprintf) == 0) {
        LOGI("Module loaded");
    } else {
        LOGE("Hook failed");
    }
}