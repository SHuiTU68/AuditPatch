#include <android/log.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
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

static int (*old_vasprintf)(char **strp, const char *fmt, va_list ap) = NULL;

static char g_target[64];
static size_t g_target_len;
static const char *g_src[2];
static size_t g_src_len[2];
static bool g_ready = false;

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

static int my_vasprintf(char **strp, const char *fmt, va_list ap) {
    int result = old_vasprintf(strp, fmt, ap);
    if (result <= 0 || *strp == NULL || !g_ready) {
        return result;
    }

    const char *s = *strp;
    size_t n = (size_t) result;
    size_t i;
    size_t growth = 0;
    bool in_quote = false;
    int k;

    // First pass: measure extra space needed, single scan, no allocation.
    for (i = 0; i < n; ++i) {
        char c = s[i];
        if (c == '"') { in_quote = !in_quote; continue; }
        if (in_quote || c != 't') { continue; }
        size_t rem = n - i;
        for (k = 0; k < 2; ++k) {
            if (match_src(s + i, rem, k)) {
                growth += g_target_len - g_src_len[k];
                i += g_src_len[k] - 1;
                break;
            }
        }
    }

    if (growth == 0) {
        return result;
    }

    char *out = (char *) malloc(n + growth + 1);
    if (out == NULL) {
        return result;
    }

    // Second pass: build the rewritten string.
    size_t o = 0;
    in_quote = false;
    for (i = 0; i < n; ++i) {
        char c = s[i];
        if (c == '"') { in_quote = !in_quote; out[o++] = c; continue; }
        if (!in_quote && c == 't') {
            size_t rem = n - i;
            bool matched = false;
            for (k = 0; k < 2; ++k) {
                if (match_src(s + i, rem, k)) {
                    memcpy(out + o, g_target, g_target_len);
                    o += g_target_len;
                    i += g_src_len[k] - 1;
                    matched = true;
                    break;
                }
            }
            if (matched) { continue; }
        }
        out[o++] = c;
    }
    out[o] = '\0';

    free(*strp);
    *strp = out;
    return (int) o;
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

    char sym[32];
    char lib[16];
    deobf(sym, enc_vasprintf, sizeof(enc_vasprintf));
    deobf(lib, enc_libc, sizeof(enc_libc));

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
