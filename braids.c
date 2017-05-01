#include <stdio.h>
#include <stdlib.h>

typedef int* perm;
typedef int* desc_cycle;
typedef struct {
    int q, l;
    perm* perm_factors;
} braid;

int factor_comp(int n, int *a, int *b) {
    int res = 0;
    for(int i = 1; i <= n; i++)
        res |= a[i] ^ b[i];
    return !res;
}

void factor_copy(int n, int *a, int *b) {
    for(int i = 1; i <= n; i++)
        b[i] = a[i];
}

void factor_print(int n, int *a) {
    for(int i = 1; i <= n; i++)
        printf("%d ", a[i]);
    printf("\n");
}

void perm_product(int n, perm a, perm b, perm c) {
    for(int i = 1; i <= n; i++)
        c[i] = b[a[i]];
}

void perm_inverse(int n, perm a, perm b) {
    for(int i = 1; i <= n; i++)
        b[a[i]] = i;
}

void delta(int n, perm d) {
    for(int i = 1; i < n; i++)
        d[i] = i + 1;
    d[n] = 1;
}

void trivial(int n, perm e) {
    for(int i = 1; i <= n; i++)
        e[i] = i;
}

// Convert a permutation table to a descending cycle decomposition table
void perm_to_desc_cycle(int n, perm a, desc_cycle x) {
    perm b = (perm)malloc(sizeof(int) * n+1);
    perm_inverse(n, a, b);
    for(int i = 1; i <= n; i++)
        x[i] = 0;
    for(int i = n; i >= 1; i--) {
        // if(x[i] == 0)
        //     x[i] = i;
        int cond = (x[i] == 0);
        x[i] = cond * i + (1 - cond) * x[i];

        // if(a[i] < i)
        //    x[a[i]] = x[i];
        cond = (b[i] < i);
        x[b[i]] = cond * x[i] + (1 - cond) * x[b[i]];
    }
    free(b);
}

// Convert a descending cycle decomposition table to a permutation table
void desc_cycle_to_perm(int n, desc_cycle x, perm a) {
    int *z = (int*)malloc(sizeof(int) * (n+1));
    for(int i = 1; i <= n; i++)
        z[i] = 0;
    for(int i = 1; i <= n; i++) {
        int cond = (z[x[i]] == 0);
        a[i] = cond * x[i] + (1 - cond) * z[x[i]];
        z[x[i]] = i;
    }
    perm_inverse(n, a, z);
    factor_copy(n, z, a);
    free(z);
}

void tau(int n, int u, perm a, perm b) {
    u %= n;
    perm *powers[2];
    // powers[1] = powers[0]^-1
    powers[0] = (perm*)malloc(sizeof(perm) * n);
    powers[1] = (perm*)malloc(sizeof(perm) * n);
    for(int i = 0; i < n; i++) {
        powers[0][i] = (perm)malloc(sizeof(int) * (n+1));
        powers[1][i] = (perm)malloc(sizeof(int) * (n+1));
    }

    trivial(n, powers[0][0]);
    trivial(n, powers[1][0]);
    delta(n, powers[0][1]);
    perm_inverse(n, powers[0][1], powers[1][1]);
    for(int i = 2; i < n; i++) {
        perm_product(n, powers[0][1], powers[0][i-1], powers[0][i]);
        perm_inverse(n, powers[0][i], powers[1][i]);
    }

    int cond = (u >= 0);
    perm l = powers[cond][u];
    perm r = powers[1 - cond][u];
    perm_product(n, l, a, b);
    perm_product(n, b, r, b);

    for(int i = 0; i < n; i++) {
        free(powers[0][i]);
        free(powers[1][i]);
    }
    free(powers[0]);
    free(powers[1]);
}

void counting_sort(int n, int **a, int **b, int digit) {
    int *c = (int*)malloc(sizeof(int) * (n+1));
    for(int i = 1; i <= n; i++)
        c[i] = 0;
    for(int i = 1; i <= n; i++)
        c[a[i][digit]] += 1;
    // c[i] now contains the number of elements equal to i
    for(int i = 2; i <= n; i++)
        c[i] += c[i - 1];
    // c[i] now contains the number of elements <= i
    for(int i = n; i >= 1; i--) {
        b[c[a[i][digit]]] = a[i];
        c[a[i][digit]]--;
    }
    free(c);
}

void radix_sort(int n, int d, int **a) {
    int **b = (int**)malloc(sizeof(int*) * (n+1));
    for(int digit = d - 1; digit >= 0; digit--) {

        counting_sort(n, a, b, digit);
        // printf("%d\n", digit);
        for(int i = 1; i <= n; i++) {
            a[i] = b[i];
            // printf("%d %d %d\n", a[i][0], a[i][1], a[i][2]);
            b[0] = 0;
        }
        // printf("\n");
    }
    free(b);
}

// compute the meet of two canonical factors in band-generator presentation
void meet(int n, perm x, perm y, perm z) {
    desc_cycle a = (desc_cycle)malloc(sizeof(int) * (n+1));
    perm_to_desc_cycle(n, x, a);
    desc_cycle b = (desc_cycle)malloc(sizeof(int) * (n+1));
    perm_to_desc_cycle(n, y, b);
    desc_cycle c = (desc_cycle)malloc(sizeof(int) * (n+1));

    desc_cycle u = (desc_cycle)malloc(sizeof(int) * (n+1));
    for(int i = 1; i <= n; i++)
        u[i] = n - i + 1;

    // radix sort u[1]...u[n] such that (a[u[i]], b[u[i]], u[i]) descending
    int **triple_perm = (int**)malloc(sizeof(int*) * (n+1));
    for(int i = 1; i <= n; i++) {
        triple_perm[i] = (int*)malloc(sizeof(int) * 3);
        triple_perm[i][0] = a[u[i]];
        triple_perm[i][1] = b[u[i]];
        triple_perm[i][2] = u[i];
        // printf("%d, %d, %d\n", triple_perm[i][0], triple_perm[i][1], triple_perm[i][2]);
    }

    // printf("\n");

    radix_sort(n, 3, triple_perm);
    for(int i = 1; i <= n; i++) {
        u[i] = triple_perm[i][2];
        // printf("%d, %d, %d\n", triple_perm[i][0], triple_perm[i][1], triple_perm[i][2]);
    }
    // printf("\n");

    for(int i = 1; i <= n; i++) {
        free(triple_perm[i]);
    }
    free(triple_perm);

    int j = u[n];
    c[j] = j;
    for(int i = n - 1; i >= 1; i--) {
        int cond = ((a[j] != a[u[i]]) | (b[j] != b[u[i]]));
        j = cond * u[i] + (1 - cond) * j;
        c[u[i]] = j;
    }

    desc_cycle_to_perm(n, c, z);

    free(a);
    free(b);
    free(c);
    free(u);
}

void braid_product(int n, braid a, braid b, braid c) {
    c.q = a.q + b.q;
    c.l = a.l + b.l;
    c.perm_factors = (perm*)malloc(sizeof(perm) * c.l);
    for(int i = 0; i < a.l; i++) {
        c.perm_factors[i] = (perm)malloc(sizeof(int) * (n + 1));
        tau(n, b.q, a.perm_factors[i], c.perm_factors[i]);
    }
    for(int i = 0; i < b.l; i++) {
        c.perm_factors[i + a.l] = (perm)malloc(sizeof(int) * (n + 1));
        for(int j = 1; j <= n; j++)
            c.perm_factors[i + a.l][j] = b.perm_factors[i][j];
    }
}

void braid_inverse(int n, braid a, braid b) {
    b.q = -a.q - a.l;
    b.l = a.l;
    b.perm_factors = (perm*)malloc(sizeof(perm) * a.l);
    perm d = (perm)malloc(sizeof(int) * (n + 1));
    delta(n, d);
    perm t1= (perm)malloc(sizeof(int) * (n + 1));
    perm t2= (perm)malloc(sizeof(int) * (n + 1));
    for(int i = 0; i < a.l; i++) {
        b.perm_factors[i] = (perm)malloc(sizeof(int) * (n + 1));
        perm_inverse(n, a.perm_factors[i], t1);
        perm_product(n, t1, d, t2);
        tau(n, -a.q-i-1, t2, b.perm_factors[b.l - i - 1]);
    }
    free(d);
    free(t1);
    free(t2);
}

// Convert a braid into the left canonical form
void canonical(int n, braid in, braid *out) {
    braid beta;
    beta.l = in.l;
    beta.perm_factors = (perm*)malloc(sizeof(perm) * beta.l);
    int l = beta.l;
    for(int i = 0; i < l; i++) {
        beta.perm_factors[i] = (perm)malloc(sizeof(int) * (n + 1));
        factor_copy(n, in.perm_factors[i], beta.perm_factors[i]);
    }
    perm d = (perm)malloc(sizeof(int) * (n + 1));
    delta(n, d);
    perm e = (perm)malloc(sizeof(int) * (n + 1));
    trivial(n, e);
    for(int i = 0; i < l; i++) {
        for(int j = l - 2; j >= i; j--) {
            perm t1 = (perm)malloc(sizeof(int) * (n + 1));
            perm_inverse(n, beta.perm_factors[j], t1);
            perm t2 = (perm)malloc(sizeof(int) * (n + 1));
            perm_product(n, t1, d, t2);
            perm b = (perm)malloc(sizeof(int) * (n + 1));
            meet(n, t2, beta.perm_factors[j+1], b);
            perm b_inv = (perm)malloc(sizeof(int) * (n + 1));
            perm_inverse(n, b, b_inv);

            perm_product(n, beta.perm_factors[j], b, beta.perm_factors[j]);
            perm_product(n, b_inv, beta.perm_factors[j+1], t1);
            factor_copy(n, t1, beta.perm_factors[j+1]);

            free(t1);
            free(t2);
            free(b);
            free(b_inv);
        }
    }
    //
    // remove factors of d and e
    int start = 0, end = l;
    for(int i = 0; i < l; i++) {
        int cond = factor_comp(n, beta.perm_factors[i], d);
        start = cond * (i + 1) + (1 - cond) * start;
        cond = factor_comp(n, beta.perm_factors[i], e);
        end = (1 - cond) * (i + 1) + cond * end;
    }
    out->q = beta.q + start;
    out->l = end - start;
    out->perm_factors = (perm*)malloc(sizeof(perm) * out->l);
    for(int i = 0; i < out->l; i++) {
        out->perm_factors[i] = (perm)malloc(sizeof(int) * (n + 1));
        factor_copy(n, beta.perm_factors[start + i], out->perm_factors[i]);
    }

    for(int i = 0; i < l; i++) {
        free(beta.perm_factors[i]);
    }
    free(beta.perm_factors);

    free(d);
    free(e);
}

int braid_comp(int n, braid a1, braid a2) {
    braid *b1 = (braid*)malloc(sizeof(braid));
    braid *b2 = (braid*)malloc(sizeof(braid));
    canonical(n, a1, b1);
    canonical(n, a2, b2);

    if(b1->l != b2->l) {
        for(int i = 0; i < b1->l; i++)
            free(b1->perm_factors[i]);
        for(int i = 0; i < b2->l; i++)
            free(b2->perm_factors[i]);
        free(b1->perm_factors);
        free(b2->perm_factors);
        return 0;
    }

    int res = 0;
    res |= b1->q ^ b2->q;

    for(int i = 0; i < b1->l; i++) {
        res |= !factor_comp(n, b1->perm_factors[i], b2->perm_factors[i]);
        free(b1->perm_factors[i]);
        free(b2->perm_factors[i]);
    }

    free(b1->perm_factors);
    free(b2->perm_factors);
    free(b1);
    free(b2);

    return !res;
}

perm band_generator(int n, int t, int s, int inverse) {
    perm canonical[2];

    canonical[0] = (perm)malloc(sizeof(int) * (n+1));   // a_ts
    trivial(n, canonical[0]);
    canonical[0][t] = s;
    canonical[0][s] = t;

    canonical[1] = (perm)malloc(sizeof(int) * (n+1));   // delta * a_ts^-1
    delta(n, canonical[1]);
    int temp = canonical[1][t];
    canonical[1][t] = canonical[1][s];
    canonical[1][s] = temp;

    free(canonical[1 - inverse]);
    return canonical[inverse];
}

braid word_to_braid(int n, int l, int **gens) {
    braid beta = {0, l, NULL};
    beta.perm_factors = (perm*)malloc(sizeof(perm) * l);
    for(int i = l-1; i >= 0; i--) {
        beta.perm_factors[i] = (perm)malloc(sizeof(int) * (n + 1));
        perm gen = band_generator(n, gens[l][0], gens[l][1], gens[l][2]);
        tau(n, beta.q, gen, beta.perm_factors[i]);

        beta.q -= gens[l][2];
    }
    return beta;
}

int main() {
    int n = 10;
    braid a = {0, 2, NULL};
    a.perm_factors = (perm*)malloc(sizeof(perm) * a.l);
    // for(int i = 0; i < a.l; i++)
    //     a.perm_factors[i] = (perm)malloc(sizeof(int) * (n+1));
    braid b = {0, 2, NULL};
    b.perm_factors = (perm*)malloc(sizeof(perm) * b.l);
    // for(int i = 0; i < b.l; i++)
    //     b.perm_factors[i] = (perm)malloc(sizeof(int) * (n+1));

    // verify far commutativity
    // a_ts a_rq = a_rq a_ts    for parallel transpositions
    for(int t = 2; t <= n; t++) {
        for(int s = 1; s < t; s++) {
            a.perm_factors[0] = band_generator(n, t, s, 0);
            b.perm_factors[1] = band_generator(n, t, s, 0);

            for(int r = 2; r < t; r++) {
                for(int q = 1; q < r; q++) {
                    if((t-r)*(t-q)*(s-r)*(s-q) > 0) {
                        a.perm_factors[1] = band_generator(n, r, q, 0);
                        b.perm_factors[0] = band_generator(n, r, q, 0);

                        if(!braid_comp(n, a, b)) {
                            printf("error: %d %d %d %d\n", t, s, r, q);
                        }

                        free(a.perm_factors[1]);
                        free(b.perm_factors[0]);
                    }
                }
            }
            free(a.perm_factors[0]);
            free(b.perm_factors[1]);
        }
    }

    // verify partial commutativity
    // a _ts a_sr = a_tr a_ts = a_sr a_tr
    for(int t = 3; t <= n; t++) {
        for(int s = 2; s < t; s++) {
            for(int r = 1; r < s; r++) {
                a.perm_factors[0] = band_generator(n, t, s, 0);
                a.perm_factors[1] = band_generator(n, s, r, 0);

                b.perm_factors[0] = band_generator(n, t, r, 0);
                b.perm_factors[1] = band_generator(n, t, s, 0);

                if(!braid_comp(n, a, b)) {
                    printf("error: %d %d %d %d\n", t, s, r, 0);
                }

                free(a.perm_factors[0]);
                a.perm_factors[0] = a.perm_factors[1];
                a.perm_factors[1] = b.perm_factors[0];

                if(!braid_comp(n, a, b)) {
                    printf("error: %d %d %d %d\n", t, s, r, 1);
                }

                free(a.perm_factors[0]);

                free(b.perm_factors[0]);
                free(b.perm_factors[1]);
            }
        }
    }

    // a.perm_factors[0] = band(n, 2, 1, 0);
    // a.perm_factors[1] = band(n, 3, 2, 0);
    // a.perm_factors[2] = band(n, 2, 1, 0);

    // b.perm_factors[0] = band(n, 3, 2, 0);
    // b.perm_factors[1] = band(n, 2, 1, 0);
    // b.perm_factors[2] = band(n, 3, 2, 0);
    // 
    // printf("%d\n", braid_comp(n, a, b));

    // for(int i = 0; i < a.l; i++) {
    //     free(a.perm_factors[i]);
    // }
    free(a.perm_factors);
    // for(int i = 0; i < b.l; i++) {
    //     free(b.perm_factors[i]);
    // }
    free(b.perm_factors);
}
