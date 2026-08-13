#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <stdlib.h>

enum {
    MAX_EXPR_DEPTH = 128,
    DEC_DIGITS     = 15,
    LINE_BUF_SIZE  = 1024
};

enum {
    CMP_GT,
    CMP_LT,
    CMP_GE,
    CMP_LE,
    CMP_EQ,
    CMP_NE
};

typedef struct {
    int64_t n;
    int64_t d;
} Frac;

typedef struct {
    const char *src;
    size_t pos;
    int depth;
    const char *err_msg;
} FCalcContext;

static int neg_i64(int64_t x, int64_t *out)
{
    if (x == INT64_MIN) return -1;
    *out = -x;
    return 0;
}

static uint64_t umag(int64_t x)
{
    return x < 0 ? 0ULL - (uint64_t)x : (uint64_t)x;
}

static uint64_t ugcd(uint64_t a, uint64_t b)
{
    while (b) {
        uint64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sadd(int64_t a, int64_t b, int64_t *r)
{
    if (a == INT64_MIN || b == INT64_MIN) return -1;
    if (b > 0 && a > INT64_MAX - b) return -1;
    if (b < 0 && a < -INT64_MAX - b) return -1;
    *r = a + b;
    if (*r == INT64_MIN) return -1;
    return 0;
}

static int smul(int64_t a, int64_t b, int64_t *r)
{
    int neg;
    uint64_t ua, ub, ur;
    if (a == INT64_MIN || b == INT64_MIN) return -1;
    neg = (a < 0) != (b < 0);
    ua = umag(a);
    ub = umag(b);
    if (ua != 0 && ub > (uint64_t)INT64_MAX / ua) return -1;
    ur = ua * ub;
    if (ur > (uint64_t)INT64_MAX) return -1;
    *r = neg ? -(int64_t)ur : (int64_t)ur;
    return 0;
}

static void fail(FCalcContext *ctx, const char *m)
{
    if (ctx && !ctx->err_msg) ctx->err_msg = m;
}

static int cmp_ufrac(uint64_t a, uint64_t b, uint64_t c, uint64_t d)
{
    int sign = 1;
    for (;;) {
        uint64_t qa = a / b;
        uint64_t qb = c / d;
        if (qa != qb) {
            int res = (qa < qb) ? -1 : 1;
            return sign == 1 ? res : -res;
        }
        uint64_t ra = a % b;
        uint64_t rc = c % d;
        if (ra == 0 && rc == 0) return 0;
        if (ra == 0) return sign == 1 ? -1 : 1;
        if (rc == 0) return sign == 1 ? 1 : -1;
        a = b;
        b = ra;
        c = d;
        d = rc;
        sign = -sign;
    }
}

static int fcmp(FCalcContext *ctx, Frac a, Frac b)
{
    if (a.d <= 0 || b.d <= 0 || a.n == INT64_MIN || b.n == INT64_MIN) {
        fail(ctx, "overflow");
        return 0;
    }
    if (a.n < 0 && b.n >= 0) return -1;
    if (a.n >= 0 && b.n < 0) return 1;
    int res = cmp_ufrac(umag(a.n), (uint64_t)a.d, umag(b.n), (uint64_t)b.d);
    if (a.n < 0) return -res;
    return res;
}

static Frac bool_frac(int x)
{
    Frac r = {0, 1};
    if (x) r.n = 1;
    return r;
}

static Frac frac_red(FCalcContext *ctx, int64_t n, int64_t d)
{
    Frac f = {0, 1};
    uint64_t un, ud, g;
    if (d == 0) {
        fail(ctx, "division by zero");
        return f;
    }
    if (n == INT64_MIN || d == INT64_MIN) {
        fail(ctx, "overflow");
        return f;
    }
    if (d < 0) {
        int64_t td;
        if (neg_i64(n, &n) != 0 || neg_i64(d, &td) != 0) {
            fail(ctx, "overflow");
            return f;
        }
        d = td;
    }
    un = umag(n);
    ud = (uint64_t)d;
    g  = ugcd(un, ud);
    f.n = n / (int64_t)g;
    f.d = d / (int64_t)g;
    return f;
}

static Frac fadd(FCalcContext *ctx, Frac a, Frac b)
{
    Frac r = {0, 1};
    int64_t g, ad, bd, n1, n2, num, den;
    if (a.d <= 0 || b.d <= 0 || a.n == INT64_MIN || b.n == INT64_MIN) {
        fail(ctx, "overflow");
        return r;
    }
    g  = (int64_t)ugcd((uint64_t)a.d, (uint64_t)b.d);
    ad = a.d / g;
    bd = b.d / g;
    if (smul(a.n, bd, &n1) ||
        smul(b.n, ad, &n2) ||
        sadd(n1, n2, &num) ||
        smul(ad, b.d, &den)) {
        fail(ctx, "overflow");
        return r;
    }
    return frac_red(ctx, num, den);
}

static Frac fsub(FCalcContext *ctx, Frac a, Frac b)
{
    Frac nb = {0, 1};
    if (b.d <= 0 || b.n == INT64_MIN) {
        fail(ctx, "overflow");
        return nb;
    }
    if (neg_i64(b.n, &nb.n) != 0) {
        fail(ctx, "overflow");
        return nb;
    }
    nb.d = b.d;
    return fadd(ctx, a, nb);
}

static Frac fmul(FCalcContext *ctx, Frac a, Frac b)
{
    Frac r = {0, 1};
    int64_t g1, g2, n, d;
    if (a.d <= 0 || b.d <= 0 || a.n == INT64_MIN || b.n == INT64_MIN) {
        fail(ctx, "overflow");
        return r;
    }
    g1 = (int64_t)ugcd(umag(a.n), (uint64_t)b.d);
    g2 = (int64_t)ugcd(umag(b.n), (uint64_t)a.d);
    if (smul(a.n / g1, b.n / g2, &n) ||
        smul(a.d / g2, b.d / g1, &d)) {
        fail(ctx, "overflow");
        return r;
    }
    r.n = n;
    r.d = d;
    return r;
}

static Frac fdiv(FCalcContext *ctx, Frac a, Frac b)
{
    Frac inv = {0, 1};
    if (b.n == 0) {
        fail(ctx, "division by zero");
        return inv;
    }
    if (a.d <= 0 || b.d <= 0 || b.n == INT64_MIN) {
        fail(ctx, "overflow");
        return inv;
    }
    if (b.n < 0) {
        if (neg_i64(b.d, &inv.n) != 0) {
            fail(ctx, "overflow");
            return inv;
        }
    } else {
        inv.n = b.d;
    }
    inv.d = (int64_t)umag(b.n);
    return fmul(ctx, a, inv);
}

static Frac fpercent(FCalcContext *ctx, Frac v)
{
    Frac r = {0, 1};
    int64_t g;
    int64_t d;
    if (v.d <= 0 || v.n == INT64_MIN) {
        fail(ctx, "overflow");
        return r;
    }
    g = (int64_t)ugcd(umag(v.n), 100ULL);
    if (smul(v.d, 100 / g, &d) != 0) {
        fail(ctx, "overflow");
        return r;
    }
    r.n = v.n / g;
    r.d = d;
    return r;
}

static void skipws(FCalcContext *ctx)
{
    while (ctx->src[ctx->pos] == ' ' || ctx->src[ctx->pos] == '\t') ctx->pos++;
}

static int peek(FCalcContext *ctx)
{
    skipws(ctx);
    return (unsigned char)ctx->src[ctx->pos];
}

static Frac parse_full(FCalcContext *ctx);
static Frac parse_equality(FCalcContext *ctx);
static Frac parse_relational(FCalcContext *ctx);
static Frac parse_additive(FCalcContext *ctx);
static Frac parse_term(FCalcContext *ctx);
static Frac parse_unary(FCalcContext *ctx);
static Frac parse_postfix(FCalcContext *ctx);
static Frac parse_primary(FCalcContext *ctx);

static Frac parse_number(FCalcContext *ctx)
{
    Frac f = {0, 1};
    int64_t n = 0;
    int64_t d = 1;
    int dot = 0;
    int any = 0;
    for (;; ctx->pos++) {
        unsigned char c = (unsigned char)ctx->src[ctx->pos];
        if (c >= '0' && c <= '9') {
            int dig = c - '0';
            if (n > (INT64_MAX - dig) / 10) {
                fail(ctx, "number too large");
                return f;
            }
            n = n * 10 + dig;
            any = 1;
            if (dot) {
                if (d > INT64_MAX / 10) {
                    fail(ctx, "number too long");
                    return f;
                }
                d *= 10;
            }
        } else if (c == '.' && !dot) {
            dot = 1;
        } else {
            break;
        }
    }
    if (!any) {
        fail(ctx, "invalid number");
        return f;
    }
    return frac_red(ctx, n, d);
}

static Frac parse_primary(FCalcContext *ctx)
{
    Frac v = {0, 1};
    int c = peek(ctx);
    if ((c >= '0' && c <= '9') || c == '.') {
        return parse_number(ctx);
    }
    if (c == '(') {
        ctx->pos++;
        v = parse_full(ctx);
        if (ctx->err_msg) return v;
        if (peek(ctx) != ')') {
            fail(ctx, "missing ')'");
            return v;
        }
        ctx->pos++;
        return v;
    }
    fail(ctx, c == '\0' ? "unexpected end of input" : "unexpected character");
    return v;
}

static Frac parse_postfix(FCalcContext *ctx)
{
    Frac v = {0, 1};
    v = parse_primary(ctx);
    while (!ctx->err_msg && peek(ctx) == '%') {
        ctx->pos++;
        v = fpercent(ctx, v);
    }
    return v;
}

static Frac parse_unary(FCalcContext *ctx)
{
    Frac v = {0, 1};
    int neg = 0;
    int c;
    for (;;) {
        c = peek(ctx);
        if (c == '-') {
            ctx->pos++;
            neg = !neg;
        } else if (c == '+') {
            ctx->pos++;
        } else {
            break;
        }
    }
    v = parse_postfix(ctx);
    if (!ctx->err_msg && neg) {
        int64_t t;
        if (neg_i64(v.n, &t) != 0) {
            fail(ctx, "overflow");
            return v;
        }
        v.n = t;
    }
    return v;
}

static Frac parse_term(FCalcContext *ctx)
{
    Frac v = {0, 1};
    Frac r = {0, 1};
    v = parse_unary(ctx);
    for (;;) {
        int c;
        if (ctx->err_msg) break;
        c = peek(ctx);
        if (c == '*' || c == 'x' || c == 'X') {
            ctx->pos++;
            r = parse_unary(ctx);
            if (!ctx->err_msg) v = fmul(ctx, v, r);
        } else if (c == '/') {
            ctx->pos++;
            r = parse_unary(ctx);
            if (!ctx->err_msg) v = fdiv(ctx, v, r);
        } else if (c == '(') {
            r = parse_unary(ctx);
            if (!ctx->err_msg) v = fmul(ctx, v, r);
        } else {
            break;
        }
    }
    return v;
}

static Frac parse_additive(FCalcContext *ctx)
{
    Frac v = {0, 1};
    Frac r = {0, 1};
    v = parse_term(ctx);
    for (;;) {
        int c;
        if (ctx->err_msg) break;
        c = peek(ctx);
        if (c == '+') {
            ctx->pos++;
            r = parse_term(ctx);
            if (!ctx->err_msg) v = fadd(ctx, v, r);
        } else if (c == '-') {
            ctx->pos++;
            r = parse_term(ctx);
            if (!ctx->err_msg) v = fsub(ctx, v, r);
        } else {
            break;
        }
    }
    return v;
}

static Frac parse_relational(FCalcContext *ctx)
{
    Frac v = {0, 1};
    Frac r = {0, 1};
    v = parse_additive(ctx);
    for (;;) {
        int op = -1;
        size_t adv = 0;
        unsigned char c;
        if (ctx->err_msg) break;
        skipws(ctx);
        c = (unsigned char)ctx->src[ctx->pos];
        if (c == '>') {
            if ((unsigned char)ctx->src[ctx->pos + 1] == '=') {
                op = CMP_GE;
                adv = 2;
            } else {
                op = CMP_GT;
                adv = 1;
            }
        } else if (c == '<') {
            if ((unsigned char)ctx->src[ctx->pos + 1] == '=') {
                op = CMP_LE;
                adv = 2;
            } else {
                op = CMP_LT;
                adv = 1;
            }
        } else {
            break;
        }
        ctx->pos += adv;
        r = parse_additive(ctx);
        if (!ctx->err_msg) {
            int cval = fcmp(ctx, v, r);
            int truth = 0;
            if (ctx->err_msg) break;
            if (op == CMP_GT) truth = cval > 0;
            else if (op == CMP_LT) truth = cval < 0;
            else if (op == CMP_GE) truth = cval >= 0;
            else if (op == CMP_LE) truth = cval <= 0;
            v = bool_frac(truth);
        }
    }
    return v;
}

static Frac parse_equality(FCalcContext *ctx)
{
    Frac v = {0, 1};
    Frac r = {0, 1};
    v = parse_relational(ctx);
    for (;;) {
        int op = -1;
        size_t adv = 0;
        unsigned char c;
        if (ctx->err_msg) break;
        skipws(ctx);
        c = (unsigned char)ctx->src[ctx->pos];
        if (c == '=' && (unsigned char)ctx->src[ctx->pos + 1] == '=') {
            op = CMP_EQ;
            adv = 2;
        } else if (c == '!' && (unsigned char)ctx->src[ctx->pos + 1] == '=') {
            op = CMP_NE;
            adv = 2;
        } else {
            break;
        }
        ctx->pos += adv;
        r = parse_relational(ctx);
        if (!ctx->err_msg) {
            int cval = fcmp(ctx, v, r);
            int truth = 0;
            if (ctx->err_msg) break;
            if (op == CMP_EQ) truth = (cval == 0);
            else truth = (cval != 0);
            v = bool_frac(truth);
        }
    }
    return v;
}

static Frac parse_full(FCalcContext *ctx)
{
    Frac v = {0, 1};
    if (ctx->depth >= MAX_EXPR_DEPTH) {
        fail(ctx, "expression too deep");
        return v;
    }
    ++ctx->depth;
    v = parse_equality(ctx);
    --ctx->depth;
    return v;
}

static int eval(FCalcContext *ctx, const char *s, Frac *out)
{
    Frac v = {0, 1};
    if (!ctx || !s || !out) return -1;
    ctx->src = s;
    ctx->pos = 0;
    ctx->depth = 0;
    ctx->err_msg = NULL;
    v = parse_full(ctx);
    if (!ctx->err_msg && peek(ctx) != '\0') {
        fail(ctx, "trailing input");
    }
    if (ctx->err_msg) return -1;
    *out = v;
    return 0;
}

static int show(Frac f)
{
    uint64_t un, du, q, rem;
    char digs[DEC_DIGITS + 1] = {0};
    int di = 0;
    if (f.d <= 0) {
        if (fputs("= error: invalid internal value\n", stdout) == EOF) return -1;
        return ferror(stdout) ? -1 : 0;
    }
    un = umag(f.n);
    du = (uint64_t)f.d;
    if (fputs("= ", stdout) == EOF) return -1;
    if (f.n < 0) {
        if (putchar('-') == EOF) return -1;
    }
    if (printf("%" PRIu64, un) < 0) return -1;
    if (f.d != 1) {
        if (printf("/%" PRIu64, du) < 0) return -1;
        q = un / du;
        rem = un % du;
        if (rem == 0) {
            if (printf("  (%s%" PRIu64 ")", f.n < 0 ? "-" : "", q) < 0) return -1;
        } else if (du > UINT64_MAX / 10) {
            if (fputs("  (~decimal expansion omitted)", stdout) == EOF) return -1;
        } else {
            while (rem && di < DEC_DIGITS) {
                rem *= 10;
                digs[di++] = (char)('0' + (int)(rem / du));
                rem %= du;
            }
            if (printf("  (%s%s%" PRIu64 ".",
                   rem ? "~" : "",
                   f.n < 0 ? "-" : "",
                   q) < 0) return -1;
            if (fwrite(digs, 1, (size_t)di, stdout) != (size_t)di) return -1;
            if (fputs(rem ? "...)" : ")", stdout) == EOF) return -1;
        }
    }
    if (putchar('\n') == EOF) return -1;
    return ferror(stdout) ? -1 : 0;
}

static int append_arg(char *buf, size_t bufsize, size_t *len, int need_space, const char *arg)
{
    size_t current;
    size_t remaining;
    int w;
    if (buf == NULL || len == NULL || arg == NULL) return -1;
    current = *len;
    if (current >= bufsize) return -1;
    remaining = bufsize - current;
    w = snprintf(buf + current, remaining, need_space ? " %s" : "%s", arg);
    if (w < 0 || (size_t)w >= remaining) return -1;
    *len = current + (size_t)w;
    return 0;
}

static int read_line(FILE *in, char *buf, size_t bufsize, size_t *out_len, int *out_eof, int *out_toolong, int *out_has_nul)
{
    size_t i = 0;
    int c;
    if (!in || !buf || bufsize == 0 || !out_len || !out_eof || !out_toolong || !out_has_nul) return -1;
    *out_eof = 0;
    *out_toolong = 0;
    *out_has_nul = 0;
    while (1) {
        c = fgetc(in);
        if (c == EOF) {
            if (i == 0) *out_eof = 1;
            break;
        }
        if (c == '\0') {
            *out_has_nul = 1;
        }
        if (c == '\n') {
            break;
        }
        if (i < bufsize - 1) {
            buf[i++] = (char)c;
        } else {
            *out_toolong = 1;
        }
    }
    buf[i] = '\0';
    *out_len = i;
    if (*out_toolong) {
        while (c != '\n' && c != EOF) {
            c = fgetc(in);
        }
    }
    return 0;
}

int main(int argc, char **argv)
{
    char line[LINE_BUF_SIZE];
    Frac v = {0, 1};
    size_t len = 0;
    int i;
    FCalcContext ctx = {0};
    int io_err = 0;

    if (argc > 1) {
        line[0] = '\0';
        len = 0;
        for (i = 1; i < argc; i++) {
            if (append_arg(line, sizeof(line), &len, i > 1, argv[i]) != 0) {
                fprintf(stderr, "error: command line too long\n");
                return 1;
            }
        }
        if (eval(&ctx, line, &v) == 0) {
            if (show(v) != 0) return 1;
            return 0;
        }
        fprintf(stderr, "error: %s\n", ctx.err_msg ? ctx.err_msg : "unknown error");
        return 1;
    }

    if (fputs("fcalc - exact fraction & percent calculator (hardened)\nType an expression (e.g.  1/3 + 25%),  'help'  or  'exit'.\n", stdout) == EOF) io_err = 1;

    while (!io_err) {
        int is_eof = 0;
        int is_toolong = 0;
        int has_nul = 0;

        if (fputs("calc> ", stdout) == EOF || fflush(stdout) == EOF) {
            io_err = 1;
            break;
        }

        read_line(stdin, line, sizeof(line), &len, &is_eof, &is_toolong, &has_nul);

        if (is_eof) {
            if (putchar('\n') == EOF) io_err = 1;
            break;
        }

        if (is_toolong) {
            fprintf(stderr, "error: input line too long\n");
            continue;
        }

        if (has_nul) {
            fprintf(stderr, "error: embedded null byte rejected\n");
            continue;
        }

        while (len > 0 && (line[len - 1] == '\r')) {
            line[--len] = '\0';
        }

        if (len == 0) continue;

        if (strcmp(line, "exit") == 0 || strcmp(line, "quit") == 0 || strcmp(line, "q") == 0) {
            break;
        }

        if (strcmp(line, "help") == 0 || strcmp(line, "?") == 0) {
            const char *help =
                "Numbers      integers and decimals: 42, 3.14, .5   (stored exactly)\n"
                "Operators    +  -  *  /  (  )      with the usual precedence\n"
                "             'x' or 'X' may be used instead of '*'\n"
                "Comparisons  > < <= >= == != return 1 for true, 0 for false\n"
                "Percent      n% means n/100. It is a strict postfix operator.\n"
                "             e.g. 1/2% == 50, (1/2)% == 1/200\n"
                "Fractions    every result is an exact reduced fraction:\n"
                "               1/2 + 1/3 = 5/6     0.1 + 0.2 = 3/10\n"
                "Other        unary minus (-2*3), implicit multiply 2(3+4) = 14\n"
                "             a decimal approximation is shown in parentheses\n"
                "Limits       exact signed 64-bit arithmetic in [-INT64_MAX, INT64_MAX]\n"
                "             INT64_MIN is intentionally rejected as overflow\n"
                "Commands     help, exit\n"
                "CLI          fcalc \"1/2 + 25%\"\n";
            if (fputs(help, stdout) == EOF) io_err = 1;
            continue;
        }

        if (eval(&ctx, line, &v) == 0) {
            if (show(v) != 0) io_err = 1;
        } else {
            fprintf(stderr, "error: %s\n", ctx.err_msg ? ctx.err_msg : "unknown error");
        }
    }

    if (io_err || ferror(stdout)) {
        return 1;
    }
    return 0;
}