/*
    Copyright 2018 0KIMS association.

    This file is part of circom (Zero Knowledge Circuit Compiler).

    circom is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    circom is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with circom. If not, see <https://www.gnu.org/licenses/>.
*/
pragma circom 2.0.0;

include "constants.circom";
include "t1.circom";
include "t2.circom";
include "../binsum.circom";
include "sigmaplus.circom";
include "sha256compression_function.circom";

/*
*** Sha256compression(): Takes a hash value and a message blocked and produces a new hash value.
        - Inputs: hin[256] -> A 256-bit intermediate hash value
                                satisfies tag binary
                  inp[512] -> A message block of 512-bits
                                satisfies tag binary
        - Outputs: out[256] -> A 256-bit new intermediate hash value
                                satisfies tag binary
         
    
*/

template Sha256compression() {
    signal input {binary} hin[256];
    signal input {binary} inp[512];
    signal output {binary} out[256];
    signal {binary} a[65][32];
    signal {binary} b[65][32];
    signal {binary} c[65][32];
    signal {binary} d[65][32];
    signal {binary} e[65][32];
    signal {binary} f[65][32];
    signal {binary} g[65][32];
    signal {binary} h[65][32];
    signal {binary} w[64][32];


    var outCalc[256] = sha256compression(hin, inp);

    var i;
    for (i=0; i<256; i++) out[i] <-- outCalc[i];

    component sigmaPlus[48];
    for (i=0; i<48; i++) sigmaPlus[i] = SigmaPlus();

    component ct_k[64];
    for (i=0; i<64; i++) ct_k[i] = K(i);

    component t1[64];
    for (i=0; i<64; i++) t1[i] = T1();

    component t2[64];
    for (i=0; i<64; i++) t2[i] = T2();

    component suma[64];
    for (i=0; i<64; i++) suma[i] = BinSum(32, 2);

    component sume[64];
    for (i=0; i<64; i++) sume[i] = BinSum(32, 2);

    component fsum[8];
    for (i=0; i<8; i++) fsum[i] = BinSum(32, 2);

    var k;
    var t;

    for (t=0; t<64; t++) {
        if (t<16) {
            for (k=0; k<32; k++) {
                w[t][k] <== inp[t*32+31-k];
            }
        } else {
            sigmaPlus[t-16].in2 <== w[t-2];
            sigmaPlus[t-16].in7 <== w[t-7];
            sigmaPlus[t-16].in15 <== w[t-15];
            sigmaPlus[t-16].in16 <== w[t-16];
            w[t] <== sigmaPlus[t-16].out;
        }
    }

    for (k=0; k<32; k++ ) {
        a[0][k] <== hin[k];
        b[0][k] <== hin[32*1 + k];
        c[0][k] <== hin[32*2 + k];
        d[0][k] <== hin[32*3 + k];
        e[0][k] <== hin[32*4 + k];
        f[0][k] <== hin[32*5 + k];
        g[0][k] <== hin[32*6 + k];
        h[0][k] <== hin[32*7 + k];
    }

    for (t = 0; t<64; t++) {
            t1[t].h <== h[t];
            t1[t].e <== e[t];
            t1[t].f <== f[t];
            t1[t].g <== g[t];
            t1[t].k <== ct_k[t].out;
            t1[t].w <== w[t];

            t2[t].a <== a[t];
            t2[t].b <== b[t];
            t2[t].c <== c[t];

            sume[t].in[0] <== d[t];
            sume[t].in[1] <== t1[t].out;

            suma[t].in[0] <== t1[t].out;
            suma[t].in[1] <== t2[t].out;
        

            for (k=0; k<32; k++) {
                h[t+1][k] <== g[t][k];
                g[t+1][k] <== f[t][k];
                f[t+1][k] <== e[t][k];
                e[t+1][k] <== sume[t].out[k];
                d[t+1][k] <== c[t][k];
                c[t+1][k] <== b[t][k];
                b[t+1][k] <== a[t][k];
                a[t+1][k] <== suma[t].out[k];
            }
        
    }

    for (k=0; k<32; k++) {
        fsum[0].in[0][k] <==  hin[32*0+k];
        fsum[0].in[1][k] <==  a[64][k];
        fsum[1].in[0][k] <==  hin[32*1+k];
        fsum[1].in[1][k] <==  b[64][k];
        fsum[2].in[0][k] <==  hin[32*2+k];
        fsum[2].in[1][k] <==  c[64][k];
        fsum[3].in[0][k] <==  hin[32*3+k];
        fsum[3].in[1][k] <==  d[64][k];
        fsum[4].in[0][k] <==  hin[32*4+k];
        fsum[4].in[1][k] <==  e[64][k];
        fsum[5].in[0][k] <==  hin[32*5+k];
        fsum[5].in[1][k] <==  f[64][k];
        fsum[6].in[0][k] <==  hin[32*6+k];
        fsum[6].in[1][k] <==  g[64][k];
        fsum[7].in[0][k] <==  hin[32*7+k];
        fsum[7].in[1][k] <==  h[64][k];
    }

    for (k=0; k<32; k++) {
        out[31-k]     === fsum[0].out[k];
        out[32+31-k]  === fsum[1].out[k];
        out[64+31-k]  === fsum[2].out[k];
        out[96+31-k]  === fsum[3].out[k];
        out[128+31-k] === fsum[4].out[k];
        out[160+31-k] === fsum[5].out[k];
        out[192+31-k] === fsum[6].out[k];
        out[224+31-k] === fsum[7].out[k];
    }
}
