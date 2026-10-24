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

static const unsigned char enc_target[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x47,0x45,0x5e,0x41,0x68,0x56,0x47,0x47,0x0d,0x44,0x07,0x0d,0x54,0x02,0x06,0x05,0x1b,0x54,0x00,0x01,0x0f};
static const unsigned char enc_su[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x44,0x42,0x0d,0x44,0x07};
static const unsigned char enc_magisk[] = {0x43,0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a,0x42,0x0d,0x45,0x0d,0x5a,0x56,0x50,0x5e,0x44,0x5c,0x0d,0x44,0x07};
static const unsigned char enc_vasprintf[] = {0x41,0x56,0x44,0x47,0x45,0x5e,0x59,0x43,0x51};
static const unsigned char enc_libc[] = {0x5b,0x5e,0x55,0x54,0x19,0x44,0x58};

static const unsigned char enc_avc[] = {0x56,0x41,0x54,0x0d};
static const unsigned char enc_audit[] = {0x56,0x42,0x53,0x5e,0x43,0x1f};
static const unsigned char enc_ctx[] = {0x54,0x58,0x59,0x43,0x52,0x4f,0x43,0x0a};
static const unsigned char enc_zygote[] = {0x56,0x47,0x47,0x68,0x4d,0x4e,0x50,0x58,0x43,0x52};
static const unsigned char enc_iso[] = {0x5e,0x44,0x58,0x5b,0x56,0x43,0x52,0x53};

static int (*old_vasprintf)(char **strp, const char *fmt, va_list ap) = NULL;

static char g_target[64];
static size_t g_target_len;
static const char *g_src[2];
static size_t g_src_len[2];
static char g_avc[8];
static char g_audit[8];
static char g_ctx[16];
static char g_zygote[16];
static char g_iso[16];
static bool g_ready = false;
/* 0 = hook runs here, 1 = sandbox carrier domain (do nothing), -1 = recheck.
   A plain fork inherits the parent's verdict, so the child resets it to -1
   and re-reads its own domain on the first intercepted call. */
static volatile int g_skip = 0;

static bool in_skip_domain(void);

static void deobf(char *dst, const unsigned char *src, size_t len) {
    size_t i;
    for (i = 0; i < len; ++i) {
        dst[i] = (char)(src[i] ^ ENC_KEY);
    }
    dst[len] = '\0';
}

static inline bool match_src(const char *s, size_t rem, int k) {
    return rem >= g_src_len[k] && s[0] == g_src[k][0] &&
           memcmp(s, g_src[k], g_src_len[k]) == 0;
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

/* Gate: only audit-shaped payloads can carry the keys we rewrite. Ordinary
   log traffic returns here without ever touching a scan loop. */
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

static int my_vasprintf(char **strp, const char *fmt, va_list ap) {
    int result = old_vasprintf(strp, fmt, ap);
    if (result <= 0 || *strp == NULL || !g_ready) {
        return result;
    }

    const char *s = *strp;
    size_t n = (size_t) result;

    int sk = g_skip;
    if (sk < 0) {
        sk = in_skip_domain() ? 1 : 0;
        g_skip = sk;
    }
    if (sk) {
        return result;
    }

    if (!gate_audit(s, n)) {
        return result;
    }

    const char *p = s;
    const char *end = s + n;
    size_t growth = 0;
    bool in_quote = false;
    int k;

    /* Pass 1: measure extra space, single forward scan, zero allocation. */
    while (p < end) {
        const char *hit = (const char *) memchr(p, 't', (size_t)(end - p));
        if (hit == NULL) {
            break;
        }
        while (p < hit) {
            if (*p == '"') {
                in_quote = !in_quote;
            }
            ++p;
        }
        size_t adv = 1;
        if (!in_quote) {
            size_t rem = (size_t)(end - p);
            for (k = 0; k < 2; ++k) {
                if (match_src(p, rem, k)) {
                    growth += g_target_len - g_src_len[k];
                    adv = g_src_len[k];
                    break;
                }
            }
        }
        p += adv;
    }

    if (growth == 0) {
        return result;
    }

    char *out = (char *) malloc(n + growth + 1);
    if (out == NULL) {
        /* OOM: leave *strp untouched so the caller keeps valid ownership. */
        return result;
    }

    /* Pass 2: build the rewritten string with the exact measured size. */
    size_t o = 0;
    in_quote = false;
    p = s;
    while (p < end) {
        const char *hit = (const char *) memchr(p, 't', (size_t)(end - p));
        if (hit == NULL) {
            while (p < end) {
                out[o++] = *p++;
            }
            break;
        }
        while (p < hit) {
            if (*p == '"') {
                in_quote = !in_quote;
            }
            out[o++] = *p++;
        }
        size_t adv = 1;
        bool matched = false;
        if (!in_quote) {
            size_t rem = (size_t)(end - p);
            for (k = 0; k < 2; ++k) {
                if (match_src(p, rem, k)) {
                    memcpy(out + o, g_target, g_target_len);
                    o += g_target_len;
                    adv = g_src_len[k];
                    matched = true;
                    break;
                }
            }
        }
        if (!matched) {
            out[o++] = *p;
        }
        p += adv;
    }
    out[o] = '\0';

    free(*strp);
    *strp = out;
    return (int) o;
}

/* Detection carriers spin up a dedicated app_zygote / isolated process whose
   only traffic is selinuxfs write rejection. Installing the hook there buys
   nothing and adds a measurable timing offset, so those domains are skipped. */
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

/* Fork children must judge their own domain: the carrier process forks into
   app_zygote, and the parent's verdict does not carry over. */
static void on_fork_child(void) {
    g_skip = -1;
}

__attribute__((constructor))
static void init(void) {
    deobf(g_target, enc_target, sizeof(enc_target));
    g_target_len = strlen(g_target);

    static char su[64];
    static char magisk[64];
    deobf(su, enc_su, sizeof(enc_su));
    deobf(magisk, enc_magisk, sizeof(enc_magisk));
    g_src[0] = su;
    g_src_len[0] = strlen(su);
    g_src[1] = magisk;
    g_src_len[1] = strlen(magisk);

    deobf(g_avc, enc_avc, sizeof(enc_avc));
    deobf(g_audit, enc_audit, sizeof(enc_audit));
    deobf(g_ctx, enc_ctx, sizeof(enc_ctx));
    deobf(g_zygote, enc_zygote, sizeof(enc_zygote));
    deobf(g_iso, enc_iso, sizeof(enc_iso));

    char sym[32];
    char lib[16];
    deobf(sym, enc_vasprintf, sizeof(enc_vasprintf));
    deobf(lib, enc_libc, sizeof(enc_libc));

    g_skip = in_skip_domain() ? 1 : 0;
    pthread_atfork(NULL, NULL, on_fork_child);

    if (g_skip) {
        LOGI("Skipping sandbox carrier domain");
        return;
    }

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