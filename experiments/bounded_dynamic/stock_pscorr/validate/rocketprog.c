/* Run programs on a Rocket core AIG (rocket_synth_wrapper) and log what they store.
 *
 * Usage: rocketprog <model.aig> <spec> <cycles> <rounds> <program_seed> <powerup_seed> <out.txt>
 *
 * The AIG is simulated bit-parallel for 64 traces. Each trace has its own memory model:
 *   - instruction memory: a 4096-word program image indexed by pc[13:2]. The words at
 *     the reset vector write x1..x31 (ADDI xN, x0, imm); every other word is drawn from
 *     the allowed (mask, value) patterns, so the program satisfies the ISA constraint.
 *     The frontend model starts fetching at the reset vector after reset, follows the
 *     core's redirect requests (io_imem_req), and delivers one word per cycle when the
 *     core is ready (io_imem_resp_ready).
 *   - data memory: a 4096-word RAM indexed by addr[13:2], with HellaCache-like timing:
 *     a request accepted in cycle t takes its store data in t+1 (io_dmem_s1_data, unless
 *     io_dmem_s1_kill), and a load answers in t+2 with its tag. Stores are performed in
 *     t+1 (if not killed) and logged as (addr, data, size).
 * Program image and RAM depend only on program_seed and the round, so two models see
 * the same programs. Inputs that are neither ports nor reset (the AIGER inputs that give
 * uninitialized registers their initial values) are random per trace from powerup_seed.
 *
 * Output: one line per trace: round, trace, number of stores, FNV-1a hash of the store
 * sequence (timing ignored), number of fetched words.
 *
 * Spec lines: reset_p <pi>; vec <name> <n> <idx...> for the ports below; pattern <mask> <value>;
 * resetvec <hex>.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t W;
typedef struct { unsigned M, I, L, O, A, B, C; unsigned *ln, *li, *out, *a0, *a1; W *val, *nxt; } Aig;

static unsigned get_uint(FILE *f) { unsigned x = 0, i = 0, c; while ((c = (unsigned)getc(f)) & 0x80) x |= (c & 0x7f) << (7 * i++); return x | (c << (7 * i)); }
static void read_aig(const char *p, Aig *g) {
    FILE *f = fopen(p, "rb"); char h[256]; unsigned J = 0, F = 0; g->B = g->C = 0;
    if (!f || !fgets(h, sizeof h, f)) { perror(p); exit(2); }
    sscanf(h, "aig %u %u %u %u %u %u %u %u %u", &g->M, &g->I, &g->L, &g->O, &g->A, &g->B, &g->C, &J, &F);
    g->ln = calloc(g->L + 1, 4); g->li = calloc(g->L + 1, 4);
    for (unsigned i = 0; i < g->L; i++) { char l[128]; unsigned a, b; if (!fgets(l, sizeof l, f)) exit(2);
        int k = sscanf(l, "%u %u", &a, &b); g->ln[i] = a; g->li[i] = k == 2 ? b : 0; }
    unsigned nout = g->O ? g->O : g->B; g->out = calloc(nout + 1, 4);
    for (unsigned i = 0; i < g->O; i++) if (fscanf(f, "%u\n", &g->out[i]) != 1) exit(2);
    for (unsigned i = 0; i < g->B; i++) { unsigned x; if (fscanf(f, "%u\n", &x) != 1) exit(2); if (!g->O) g->out[i] = x; }
    for (unsigned i = 0; i < g->C; i++) { unsigned x; if (fscanf(f, "%u\n", &x) != 1) exit(2); }
    if (!g->O) g->O = g->B;
    g->a0 = malloc((g->A + 1) * 4); g->a1 = malloc((g->A + 1) * 4);
    for (unsigned i = 0; i < g->A; i++) { unsigned lhs = 2 * (g->I + g->L + 1 + i), d0 = get_uint(f), d1 = get_uint(f);
        g->a0[i] = lhs - d0; g->a1[i] = g->a0[i] - d1; }
    fclose(f); g->val = calloc(g->M + 1, sizeof(W)); g->nxt = calloc(g->L + 1, sizeof(W));
}
static inline W lit(const Aig *g, unsigned l) { W v = g->val[l >> 1]; return (l & 1) ? ~v : v; }
static void eval(Aig *g, const W *pi) { g->val[0] = 0; for (unsigned i = 0; i < g->I; i++) g->val[1 + i] = pi[i];
    unsigned b = g->I + g->L + 1; for (unsigned i = 0; i < g->A; i++) g->val[b + i] = lit(g, g->a0[i]) & lit(g, g->a1[i]); }
static void step(Aig *g) { for (unsigned i = 0; i < g->L; i++) g->nxt[i] = lit(g, g->ln[i]);
    for (unsigned i = 0; i < g->L; i++) g->val[g->I + 1 + i] = g->nxt[i]; }

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

enum { RESET, IRV, IRPC, IRDATA, IREQV, IREQPC, IRREADY, DRDY, DREQV, DADDR, DTAG, DCMD, DSIZE, DKILL, DSDATA,
       DRESPV, DRESPTAG, DRESPDATA, DHASDATA, DBYPASS, DORDERED, NV };
static const char *VN[NV] = {"reset", "io_imem_resp_valid", "io_imem_resp_bits_pc", "io_imem_resp_bits_data",
    "io_imem_req_valid", "io_imem_req_bits_pc", "io_imem_resp_ready", "io_dmem_req_ready", "io_dmem_req_valid",
    "io_dmem_req_bits_addr", "io_dmem_req_bits_tag", "io_dmem_req_bits_cmd", "io_dmem_req_bits_size",
    "io_dmem_s1_kill", "io_dmem_s1_data_data", "io_dmem_resp_valid", "io_dmem_resp_bits_tag",
    "io_dmem_resp_bits_data", "io_dmem_resp_bits_has_data", "io_dmem_resp_bits_data_word_bypass", "io_dmem_ordered"};
static int vn[NV], vi[NV][32];

static unsigned getv(Aig *g, int v, int j) { unsigned x = 0; for (int b = 0; b < vn[v]; b++) if ((lit(g, g->out[vi[v][b]]) >> j) & 1) x |= 1u << b; return x; }
static void setv(W *pi, int v, int j, unsigned x) { for (int b = 0; b < vn[v]; b++) { W m = (W)1 << j; if ((x >> b) & 1) pi[vi[v][b]] |= m; else pi[vi[v][b]] &= ~m; } }

#define IW 4096
int main(int argc, char **argv) {
    if (argc != 8) { fprintf(stderr, "usage: rocketprog model spec cycles rounds program_seed powerup_seed out\n"); return 2; }
    Aig g; read_aig(argv[1], &g);
    long cycles = atol(argv[3]), rounds = atol(argv[4]);
    uint64_t pseed = strtoull(argv[5], 0, 10), useed = strtoull(argv[6], 0, 10);
    unsigned masks[512], pats[512], resetvec = 0x80000000u; int npat = 0;
    char *isport = calloc(g.I, 1);
    FILE *sf = fopen(argv[2], "r"); char key[64];
    while (fscanf(sf, "%63s", key) == 1) {
        if (!strcmp(key, "pattern")) { if (fscanf(sf, "%x %x", &masks[npat], &pats[npat]) != 2) return 2; npat++; }
        else if (!strcmp(key, "resetvec")) { if (fscanf(sf, "%x", &resetvec) != 1) return 2; }
        else if (!strcmp(key, "port")) { int idx; if (fscanf(sf, "%d", &idx) != 1) return 2; isport[idx] = 1; }
        else if (!strcmp(key, "vec")) { char name[96]; int n; if (fscanf(sf, "%95s %d", name, &n) != 2) return 2;
            int v = -1; for (int k = 0; k < NV; k++) if (!strcmp(name, VN[k])) v = k;
            for (int b = 0; b < n; b++) { int x; if (fscanf(sf, "%d", &x) != 1) return 2; if (v >= 0 && b < 32) vi[v][b] = x; }
            if (v >= 0) vn[v] = n < 32 ? n : 32; }
        else { fprintf(stderr, "bad key %s\n", key); return 2; }
    }
    fclose(sf);
    FILE *of = fopen(argv[7], "w");
    int dump = getenv("ROCKETPROG_DUMP") ? atoi(getenv("ROCKETPROG_DUMP")) : 0;
    unsigned (*imems)[IW] = malloc(64 * sizeof(unsigned[IW])), (*dmem)[IW] = malloc(64 * sizeof(unsigned[IW]));
    W *pi = calloc(g.I, sizeof(W));
    for (long r = 0; r < rounds; r++) {
        rs = pseed * 0x9E3779B97F4A7C15ull + (uint64_t)r * 7919 + 1;
        for (int jj = 0; jj < 64; jj++) {   /* one program per trace */
        unsigned (*imem)[IW] = &imems[jj];
        for (int i = 0; i < IW; i++) {
            unsigned w;
            for (;;) {   /* trap-free code: every word still satisfies its (mask, value) pattern */
                int p = (int)(rnd() % (unsigned)npat);
                w = ((unsigned)rnd() & ~masks[p]) | pats[p];
                unsigned op = w & 0x7Fu, f3 = (w >> 12) & 7u;
                if (op == 0x73u) continue;                                   /* ECALL/EBREAK/CSR */
                if (op == 0x63u) w &= ~(1u << 8);                            /* branch offset % 4 == 0 */
                if (op == 0x6Fu) w &= ~(1u << 21);                           /* JAL offset % 4 == 0 */
                if (op == 0x67u) w &= ~((0x1Fu << 15) | (3u << 20));         /* JALR x0 + aligned imm */
                if (op == 0x03u) { w &= ~(0x1Fu << 15);                       /* loads: x0 + aligned imm */
                    if (f3 == 2) w &= ~(3u << 20); else if (f3 == 1 || f3 == 5) w &= ~(1u << 20); }
                if (op == 0x23u) { w &= ~(0x1Fu << 15);                       /* stores: x0 + aligned imm */
                    if (f3 == 2) w &= ~(3u << 7); else if (f3 == 1) w &= ~(1u << 7); }
                if ((w & masks[p]) == pats[p]) break;                        /* still allowed */
            }
            (*imem)[i] = w;
        }
        for (int k = 0; k < 31; k++)  /* ADDI x(k+1), x0, imm at the reset vector */
            (*imem)[((resetvec >> 2) + k) % IW] = ((unsigned)rnd() & 0xFFF00000u) | ((unsigned)(k + 1) << 7) | 0x13u;
        for (int i = 0; i < IW; i++) dmem[jj][i] = (unsigned)rnd();
        }
        /* power-up values of uninitialized registers */
        uint64_t ps = rs; rs = useed * 0xD1B54A32D192ED03ull + (uint64_t)r * 104729 + 3;
        W *initv = calloc(g.I, sizeof(W)); for (unsigned i = 0; i < g.I; i++) initv[i] = rnd(); rs = ps;
        for (unsigned i = 0; i < g.L; i++) g.val[g.I + 1 + i] = g.li[i] ? ~(W)0 : 0;
        unsigned fpc[64], fvalid[64] = {0}; unsigned long long hash[64]; long nst[64] = {0}, nfetch[64] = {0};
        unsigned p1v[64] = {0}, p1a[64], p1t[64], p1c[64], p1s[64], p2v[64] = {0}, p2a[64], p2t[64], p2c[64];
        for (int j = 0; j < 64; j++) { hash[j] = 1469598103934665603ull; fpc[j] = resetvec; }
        for (long t = 0; t < cycles; t++) {
            int rst = t < 16;
            for (unsigned i = 0; i < g.I; i++) pi[i] = isport[i] ? 0 : initv[i];
            setv(pi, RESET, 0, 0); for (int j = 0; j < 64; j++) setv(pi, RESET, j, rst);
            for (int j = 0; j < 64; j++) {
                setv(pi, DRDY, j, 1); setv(pi, DORDERED, j, 1);
                if (!rst && fvalid[j]) { setv(pi, IRV, j, 1); setv(pi, IRPC, j, fpc[j]); setv(pi, IRDATA, j, imems[j][(fpc[j] >> 2) % IW]); }
                else { setv(pi, IRDATA, j, imems[j][(fpc[j] >> 2) % IW]); }
                if (p2v[j] && p2c[j] == 0) {   /* load answers two cycles after acceptance */
                    unsigned d = dmem[j][(p2a[j] >> 2) % IW];
                    setv(pi, DRESPV, j, 1); setv(pi, DHASDATA, j, 1); setv(pi, DRESPTAG, j, p2t[j]);
                    setv(pi, DRESPDATA, j, d); setv(pi, DBYPASS, j, d);
                }
            }
            eval(&g, pi);
            for (int j = 0; j < 64; j++) {
                if (rst) { fvalid[j] = 1; fpc[j] = resetvec; p1v[j] = p2v[j] = 0; continue; }
                /* stage 2 <- stage 1 (unless killed); stores happen with s1 data */
                p2v[j] = 0;
                if (p1v[j] && !getv(&g, DKILL, j)) {
                    if (p1c[j] == 1) {      /* M_XWR */
                        unsigned d = getv(&g, DSDATA, j), a = p1a[j], sz = p1s[j], idx = (a >> 2) % IW, old = dmem[j][idx];
                        unsigned sh = (a & 3) * 8, m = sz == 0 ? 0xFFu << sh : sz == 1 ? 0xFFFFu << sh : 0xFFFFFFFFu;
                        dmem[j][idx] = (old & ~m) | ((d << (sz == 2 ? 0 : 0)) & m);
                        unsigned long long x = ((unsigned long long)a << 34) ^ ((unsigned long long)sz << 32) ^ (d & m);
                        hash[j] = (hash[j] ^ x) * 1099511628211ull; nst[j]++;
                        if (dump && r == 0 && j == 0 && nst[j] <= dump)
                            fprintf(stderr, "t=%ld store addr=%08x size=%u data=%08x\n", t, a, sz, d);
                    } else { p2v[j] = 1; p2a[j] = p1a[j]; p2t[j] = p1t[j]; p2c[j] = p1c[j]; }
                }
                p1v[j] = 0;
                if (getv(&g, DREQV, j)) { p1v[j] = 1; p1a[j] = getv(&g, DADDR, j); p1t[j] = getv(&g, DTAG, j);
                    p1c[j] = getv(&g, DCMD, j); p1s[j] = getv(&g, DSIZE, j); }
                /* frontend */
                if (dump && r == 0 && j == 0 && t < 200 && (getv(&g, IREQV, j) || getv(&g, IRREADY, j)))
                    fprintf(stderr, "t=%ld fetch pc=%08x word=%08x ready=%u redirect=%u->%08x\n", t, fpc[j],
                            imems[j][(fpc[j] >> 2) % IW], getv(&g, IRREADY, j), getv(&g, IREQV, j), getv(&g, IREQPC, j));
                if (getv(&g, IREQV, j)) { fpc[j] = getv(&g, IREQPC, j); fvalid[j] = 1; }
                else if (fvalid[j] && getv(&g, IRREADY, j)) { fpc[j] += 4; nfetch[j]++; }
            }
            step(&g);
        }
        for (int j = 0; j < 64; j++) fprintf(of, "%ld %d %ld %016llx %ld\n", r, j, nst[j], hash[j], nfetch[j]);
        free(initv);
    }
    fclose(of);
    return 0;
}
