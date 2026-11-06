/* Bit-parallel co-simulation of two AIGER models with constrained stimulus.
 *
 * Usage: aigcosim <pre.aig> <post.aig> <spec> <cycles> <rounds> <seed> [changed.txt [mismatch.txt]]
 *
 * With changed.txt, the indices of pre's latches that ever differ from their initial
 * value on a live trace (from cycle 1 on) are written there, one per line.
 *
 * pre.aig is the model before ABC (its AIGER constraints are the CRISP assumptions);
 * post.aig is the model after `scorr` with the constraints removed. Both have the same
 * primary inputs in the same order, and post's outputs are pre's outputs. Each round
 * simulates 64 independent traces for <cycles> cycles from the AIGER initial state.
 *
 * Every cycle the stimulus drives all primary inputs (spec below), both models are
 * evaluated, every pre constraint literal is checked (a trace stops counting after a
 * violation) and every output of post is compared with pre for traces whose
 * constraints have held so far.
 *
 * Spec lines (indices are AIGER input / output positions):
 *   reset_n <pi>                         active-low reset: low in cycle 0, rare later
 *   rereset <per-mille>                  probability of a later reset cycle
 *   word <pi0..pi31>                     32 inputs of an instruction word, bit 0 first;
 *                                        several word lines give several lanes
 *   pattern <mask> <value>               allowed (mask, value); word = rand&~mask | value
 *   const1 <pi>                          input tied to 1 (e.g. grant with grant_latency 0)
 *   tagged <maxlat> <req_po> <rdy_po|-1> <rvalid_pi> <qual_pi|-1> <tw> <reqtag_po...> <rsptag_pi...>
 *                                        tagged channel: response 1..maxlat cycles after
 *                                        acceptance, at most one per cycle, any order. With a
 *                                        qualifier input (e.g. AXI r.last) only rvalid&&qual is
 *                                        a response: it is 1 on responses, and on other cycles
 *                                        it is 0 while rvalid is random (non-final beats)
 *   inorder <maxlat> <req_po> <rdy_po|-1> <rvalid_pi>
 *                                        in-order channel, response held until taken
 *   qualify <po> <n> <q_po...>           compare output po only in cycles where the n
 *                                        outputs q_po of pre are all 1 (e.g. SRAM write
 *                                        data only while the SRAM is selected and writing)
 * All other inputs are uniformly random every cycle.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t W;

typedef struct {
    unsigned M, I, L, O, A, B, C;
    unsigned *latch_next, *latch_init, *out, *cons;
    unsigned *and0, *and1;
    W *val, *nxt;
} Aig;

static unsigned get_uint(FILE *f) {
    unsigned x = 0, i = 0, c;
    while ((c = (unsigned)getc(f)) & 0x80) x |= (c & 0x7f) << (7 * i++);
    return x | (c << (7 * i));
}

static void read_aig(const char *path, Aig *g) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    char hdr[256];
    if (!fgets(hdr, sizeof hdr, f)) { fprintf(stderr, "%s: empty\n", path); exit(2); }
    unsigned J = 0, F = 0;
    g->B = g->C = 0;
    int n = sscanf(hdr, "aig %u %u %u %u %u %u %u %u %u", &g->M, &g->I, &g->L, &g->O, &g->A, &g->B, &g->C, &J, &F);
    if (n < 5 || J || F) { fprintf(stderr, "%s: unsupported header %s", path, hdr); exit(2); }
    g->latch_next = calloc(g->L + 1, sizeof(unsigned));
    g->latch_init = calloc(g->L + 1, sizeof(unsigned));
    for (unsigned i = 0; i < g->L; i++) {
        char line[128];
        if (!fgets(line, sizeof line, f)) exit(2);
        unsigned a, b;
        int k = sscanf(line, "%u %u", &a, &b);
        g->latch_next[i] = a;
        g->latch_init[i] = (k == 2) ? b : 0;
        if (k == 2 && b != 0 && b != 1) { fprintf(stderr, "%s: uninitialized latch %u\n", path, i); exit(2); }
    }
    /* ABC writes outputs as bad-state literals when constraints are present: read them as outputs */
    unsigned nout = g->O ? g->O : g->B;
    g->out = calloc(nout + 1, sizeof(unsigned));
    for (unsigned i = 0; i < g->O; i++) if (fscanf(f, "%u\n", &g->out[i]) != 1) exit(2);
    for (unsigned i = 0; i < g->B; i++) { unsigned x; if (fscanf(f, "%u\n", &x) != 1) exit(2); if (!g->O) g->out[i] = x; }
    if (!g->O) { g->O = g->B; g->B = 0; }
    g->cons = calloc(g->C + 1, sizeof(unsigned));
    for (unsigned i = 0; i < g->C; i++) if (fscanf(f, "%u\n", &g->cons[i]) != 1) exit(2);
    g->and0 = malloc((g->A + 1) * sizeof(unsigned));
    g->and1 = malloc((g->A + 1) * sizeof(unsigned));
    for (unsigned i = 0; i < g->A; i++) {
        unsigned lhs = 2 * (g->I + g->L + 1 + i);
        unsigned d0 = get_uint(f), d1 = get_uint(f);
        g->and0[i] = lhs - d0;
        g->and1[i] = g->and0[i] - d1;
    }
    fclose(f);
    g->val = calloc(g->M + 1, sizeof(W));
    g->nxt = calloc(g->L + 1, sizeof(W));
}

static inline W lit(const Aig *g, unsigned l) { W v = g->val[l >> 1]; return (l & 1) ? ~v : v; }

static void reset_state(Aig *g) {
    for (unsigned i = 0; i < g->L; i++) g->val[g->I + 1 + i] = g->latch_init[i] ? ~(W)0 : 0;
}

static void eval(Aig *g, const W *pi) {
    g->val[0] = 0;
    for (unsigned i = 0; i < g->I; i++) g->val[1 + i] = pi[i];
    unsigned base = g->I + g->L + 1;
    for (unsigned i = 0; i < g->A; i++) g->val[base + i] = lit(g, g->and0[i]) & lit(g, g->and1[i]);
}

static void step(Aig *g) {
    for (unsigned i = 0; i < g->L; i++) g->nxt[i] = lit(g, g->latch_next[i]);
    for (unsigned i = 0; i < g->L; i++) g->val[g->I + 1 + i] = g->nxt[i];
}

/* ---- stimulus ---- */
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

#define MAXCH 8
#define MAXT 64
typedef struct {
    int tagged, maxlat, req_po, rdy_po, rvalid_pi, qual_pi, tw;
    int reqtag_po[8], rsptag_pi[8];
    /* per trace state */
    int out[64][MAXT], age[64][MAXT], due[64][MAXT];            /* tagged */
    int qn[64], qage[64][16], qdue[64][16];                        /* in order */
    int cur_rsp[64];                                               /* tag offered this cycle */
} Chan;

int main(int argc, char **argv) {
    if (argc < 7 || argc > 9) { fprintf(stderr, "usage: aigcosim pre post spec cycles rounds seed [changed.txt]\n"); return 2; }
    Aig pre, post;
    read_aig(argv[1], &pre);
    read_aig(argv[2], &post);
    long cycles = atol(argv[4]), rounds = atol(argv[5]);
    rs = strtoull(argv[6], 0, 10) * 0x9E3779B97F4A7C15ull + 1;
    if (pre.I != post.I || pre.O != post.O) {
        fprintf(stderr, "interface mismatch: pre I=%u O=%u post I=%u O=%u\n", pre.I, pre.O, post.I, post.O);
        return 2;
    }
    unsigned I = pre.I;
    char *kind = calloc(I, 1);              /* 0 random, 1 reset, 2 word bit, 3 const1, 4 driven by channel */
    int word[64][32], nlanes = 0, reset_pi = -1, rereset = 0;
    unsigned masks[512], pats[512]; int npat = 0;
    Chan *ch = calloc(MAXCH, sizeof(Chan)); int nch = 0;
    int *qn = calloc(pre.O + 1, sizeof(int)); int (*qs)[4] = calloc(pre.O + 1, sizeof(int[4]));
    FILE *sf = fopen(argv[3], "r");
    if (!sf) { perror(argv[3]); return 2; }
    char key[64];
    while (fscanf(sf, "%63s", key) == 1) {
        if (!strcmp(key, "reset_n")) { if (fscanf(sf, "%d", &reset_pi) != 1) return 2; kind[reset_pi] = 1; }
        else if (!strcmp(key, "rereset")) { if (fscanf(sf, "%d", &rereset) != 1) return 2; }
        else if (!strcmp(key, "word")) { if (nlanes == 64) return 2; for (int b = 0; b < 32; b++) { if (fscanf(sf, "%d", &word[nlanes][b]) != 1) return 2; kind[word[nlanes][b]] = 2; } nlanes++; }
        else if (!strcmp(key, "pattern")) { if (fscanf(sf, "%x %x", &masks[npat], &pats[npat]) != 2) return 2; npat++; }
        else if (!strcmp(key, "qualify")) {
            int o, n; if (fscanf(sf, "%d %d", &o, &n) != 2 || n > 4) return 2;
            qn[o] = n; for (int k = 0; k < n; k++) if (fscanf(sf, "%d", &qs[o][k]) != 1) return 2;
        }
        else if (!strcmp(key, "const1")) { int p; if (fscanf(sf, "%d", &p) != 1) return 2; kind[p] = 3; }
        else if (!strcmp(key, "tagged") || !strcmp(key, "inorder")) {
            Chan *c = &ch[nch++];
            c->tagged = !strcmp(key, "tagged");
            if (fscanf(sf, "%d %d %d %d", &c->maxlat, &c->req_po, &c->rdy_po, &c->rvalid_pi) != 4) return 2;
            kind[c->rvalid_pi] = 4;
            c->qual_pi = -1;
            if (c->tagged) {
                if (fscanf(sf, "%d %d", &c->qual_pi, &c->tw) != 2) return 2;
                if (c->qual_pi >= 0) kind[c->qual_pi] = 4;
                for (int b = 0; b < c->tw; b++) if (fscanf(sf, "%d", &c->reqtag_po[b]) != 1) return 2;
                for (int b = 0; b < c->tw; b++) { if (fscanf(sf, "%d", &c->rsptag_pi[b]) != 1) return 2; kind[c->rsptag_pi[b]] = 4; }
            }
        } else { fprintf(stderr, "bad spec key %s\n", key); return 2; }
    }
    fclose(sf);
    if (reset_pi < 0) { fprintf(stderr, "spec needs reset_n\n"); return 2; }

    W *pi = calloc(I, sizeof(W));
    W *changed = calloc(pre.L + 1, sizeof(W));
    long long *mm_out = calloc(pre.O + 1, sizeof(long long));
    long long compared = 0, mismatch_cycles = 0, violated_traces = 0, live_trace_cycles = 0;
    long long first_mm_round = -1, first_mm_cycle = -1, first_mm_out = -1;
    for (long r = 0; r < rounds; r++) {
        reset_state(&pre); reset_state(&post);
        for (int k = 0; k < nch; k++) {
            memset(ch[k].out, 0, sizeof ch[k].out); memset(ch[k].age, 0, sizeof ch[k].age);
            memset(ch[k].qn, 0, sizeof ch[k].qn);
        }
        W alive = ~(W)0, mm_any = 0;
        for (long t = 0; t < cycles; t++) {
            W rstn = ~(W)0;
            if (t == 0) rstn = 0;
            else if (rereset) for (int j = 0; j < 64; j++) if ((int)(rnd() % 1000) < rereset) rstn &= ~((W)1 << j);
            for (unsigned i = 0; i < I; i++) {
                if (kind[i] == 0) pi[i] = rnd();
                else if (kind[i] == 3) pi[i] = ~(W)0;
            }
            pi[reset_pi] = rstn;
            for (int l = 0; l < nlanes; l++) {
                for (int b = 0; b < 32; b++) pi[word[l][b]] = 0;
                for (int j = 0; j < 64; j++) {
                    unsigned w = (unsigned)rnd();
                    if (npat) { int p = (int)(rnd() % (unsigned)npat); w = (w & ~masks[p]) | pats[p]; }
                    for (int b = 0; b < 32; b++) if ((w >> b) & 1) pi[word[l][b]] |= (W)1 << j;
                }
            }
            /* channel responses decided from the model state (before this cycle's requests) */
            for (int k = 0; k < nch; k++) {
                Chan *c = &ch[k];
                pi[c->rvalid_pi] = 0;
                if (c->qual_pi >= 0) pi[c->qual_pi] = 0;
                if (c->tagged) for (int b = 0; b < c->tw; b++) pi[c->rsptag_pi[b]] = 0;
                for (int j = 0; j < 64; j++) {
                    c->cur_rsp[j] = -1;
                    if (!((rstn >> j) & 1)) continue;
                    if (c->tagged) {
                        int best = -1;
                        for (int tg = 0; tg < (1 << c->tw); tg++) if (c->out[j][tg]) {
                            if (c->age[j][tg] >= c->maxlat) { best = tg; break; }           /* deadline */
                            if (c->age[j][tg] >= c->due[j][tg] && best < 0) best = tg;
                        }
                        if (best >= 0) {
                            c->cur_rsp[j] = best;
                            pi[c->rvalid_pi] |= (W)1 << j;
                            if (c->qual_pi >= 0) pi[c->qual_pi] |= (W)1 << j;
                            for (int b = 0; b < c->tw; b++) if ((best >> b) & 1) pi[c->rsptag_pi[b]] |= (W)1 << j;
                        } else if (rnd() & 1) {
                            for (int b = 0; b < c->tw; b++) if (rnd() & 1) pi[c->rsptag_pi[b]] |= (W)1 << j;
                            if (c->qual_pi >= 0 && (rnd() & 1)) pi[c->rvalid_pi] |= (W)1 << j;  /* non-final beat */
                        }
                    } else if (c->qn[j] && c->qage[j][0] >= c->qdue[j][0]) {
                        c->cur_rsp[j] = 0;
                        pi[c->rvalid_pi] |= (W)1 << j;
                    }
                }
            }
            eval(&pre, pi);
            eval(&post, pi);
            /* constraints of pre: a trace counts only while all hold */
            for (unsigned i = 0; i < pre.C; i++) {
                W v = lit(&pre, pre.cons[i]);
                W bad = alive & ~v;
                if (bad) { violated_traces += __builtin_popcountll(bad); alive &= ~bad; }
            }
            W mm = 0;
            for (unsigned o = 0; o < pre.O; o++) {
                W d = (lit(&pre, pre.out[o]) ^ lit(&post, post.out[o])) & alive;
                for (int k = 0; k < qn[o]; k++) d &= lit(&pre, pre.out[qs[o][k]]);
                mm_out[o] += __builtin_popcountll(d);
                if (d && first_mm_round < 0) { first_mm_round = r; first_mm_cycle = t; first_mm_out = o; }
                mm |= d;
            }
            if (t >= 1)
                for (unsigned i = 0; i < pre.L; i++)
                    changed[i] |= (pre.val[pre.I + 1 + i] ^ (pre.latch_init[i] ? ~(W)0 : 0)) & alive;
            mismatch_cycles += __builtin_popcountll(mm);
            mm_any |= mm;
            live_trace_cycles += __builtin_popcountll(alive);
            compared += __builtin_popcountll(alive) * (long long)pre.O;
            /* update channel models with this cycle's handshakes */
            for (int k = 0; k < nch; k++) {
                Chan *c = &ch[k];
                W req = lit(&pre, pre.out[c->req_po]);
                W rdy = c->rdy_po >= 0 ? lit(&pre, pre.out[c->rdy_po]) : ~(W)0;
                for (int j = 0; j < 64; j++) {
                    if (!((rstn >> j) & 1)) { memset(c->out[j], 0, sizeof c->out[j]); c->qn[j] = 0; continue; }
                    int taken = c->cur_rsp[j] >= 0 && ((rdy >> j) & 1);
                    if (c->tagged) {
                        for (int tg = 0; tg < (1 << c->tw); tg++) if (c->out[j][tg] && c->age[j][tg] < c->maxlat) c->age[j][tg]++;
                        if (taken) c->out[j][c->cur_rsp[j]] = 0;
                        if ((req >> j) & 1) {   /* grant is tied high for timing channels */
                            int tg = 0;
                            for (int b = 0; b < c->tw; b++) if ((lit(&pre, pre.out[c->reqtag_po[b]]) >> j) & 1) tg |= 1 << b;
                            c->out[j][tg] = 1; c->age[j][tg] = 1; c->due[j][tg] = 1 + (int)(rnd() % (unsigned)c->maxlat);
                        }
                    } else {
                        for (int q = 0; q < c->qn[j]; q++) if (c->qage[j][q] < c->maxlat) c->qage[j][q]++;
                        if (taken) {
                            for (int q = 1; q < c->qn[j]; q++) { c->qage[j][q - 1] = c->qage[j][q]; c->qdue[j][q - 1] = c->qdue[j][q]; }
                            c->qn[j]--;
                        }
                        if (((req >> j) & 1) && c->qn[j] < 16) {
                            c->qage[j][c->qn[j]] = 1; c->qdue[j][c->qn[j]] = 1 + (int)(rnd() % (unsigned)c->maxlat); c->qn[j]++;
                        }
                    }
                }
            }
            step(&pre);
            step(&post);
        }
    }
    if (argc == 9) {
        FILE *mf = fopen(argv[8], "w");
        for (unsigned o = 0; o < pre.O; o++) if (mm_out[o]) fprintf(mf, "%u %lld\n", o, mm_out[o]);
        fclose(mf);
    }
    if (argc >= 8) {
        FILE *cf = fopen(argv[7], "w");
        for (unsigned i = 0; i < pre.L; i++) if (changed[i]) fprintf(cf, "%u\n", i);
        fclose(cf);
    }
    printf("{\"rounds\": %ld, \"traces\": %ld, \"cycles\": %ld, \"live_trace_cycles\": %lld, "
           "\"constraint_violating_traces\": %lld, \"compared_output_bits\": %lld, \"mismatch_trace_cycles\": %lld, "
           "\"first_mismatch\": [%lld, %lld, %lld]}\n",
           rounds, rounds * 64, cycles, live_trace_cycles, violated_traces, compared, mismatch_cycles,
           first_mm_round, first_mm_cycle, first_mm_out);
    return mismatch_cycles ? 1 : 0;
}
