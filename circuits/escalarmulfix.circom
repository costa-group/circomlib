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
pragma circom 2.1.5;

include "mux3.circom";
include "montgomery.circom";
include "babyjub.circom";
include "tags-specifications.circom";


// To consult the tags specifications check tags-specifications.circom

/*

*** WindowMulFix(): template that given a point in Montgomery representation base and a binary input in, calculates:
        out = base + base*in[0] + 2*base*in[1] + 4*base*in[2]
        out4 = 4*base

    This circuit is used in order to multiply a fixed point of the BabyJub curve by a escalar (k * p with p a fixed point of the curve). 
        - Inputs: in[3] -> binary value
                         requires tag binary
                  base[2] -> input curve point in Montgomery representation
        - Outputs: out[2] -> output curve point in Montgomery representation
                   out8[2] -> output curve point in Montgomery representation
    
 */
template WindowMulFix() {
    signal input {binary} in[3];
    signal input base[2];
    signal output out[2];
    signal output out8[2];   // Returns 8*Base (To be linked)

    component mux = MultiMux3(2);

    mux.s <== in;

    component dbl2 = MontgomeryDouble();
    component adr3 = MontgomeryAdd();
    component adr4 = MontgomeryAdd();
    component adr5 = MontgomeryAdd();
    component adr6 = MontgomeryAdd();
    component adr7 = MontgomeryAdd();
    component adr8 = MontgomeryAdd();

// in[0]  -> 1*BASE

    mux.c[0][0] <== base[0];
    mux.c[1][0] <== base[1];

// in[1] -> 2*BASE
    dbl2.in <== base;
    mux.c[0][1] <== dbl2.out[0];
    mux.c[1][1] <== dbl2.out[1];

// in[2] -> 3*BASE
    adr3.in1 <== base;
    adr3.in2 <== dbl2.out;
    mux.c[0][2] <== adr3.out[0];
    mux.c[1][2] <== adr3.out[1];

// in[3] -> 4*BASE
    adr4.in1 <== base;
    adr4.in2 <== adr3.out;
    mux.c[0][3] <== adr4.out[0];
    mux.c[1][3] <== adr4.out[1];

// in[4] -> 5*BASE
    adr5.in1 <== base;
    adr5.in2 <== adr4.out;
    mux.c[0][4] <== adr5.out[0];
    mux.c[1][4] <== adr5.out[1];

// in[5] -> 6*BASE
    adr6.in1 <== base;
    adr6.in2 <== adr5.out;
    mux.c[0][5] <== adr6.out[0];
    mux.c[1][5] <== adr6.out[1];

// in[6] -> 7*BASE
    adr7.in1 <== base;
    adr7.in2 <== adr6.out;
    mux.c[0][6] <== adr7.out[0];
    mux.c[1][6] <== adr7.out[1];

// in[7] -> 8*BASE
    adr8.in1 <== base;
    adr8.in2 <== adr7.out;
    mux.c[0][7] <== adr8.out[0];
    mux.c[1][7] <== adr8.out[1];

    out8 <== adr8.out;
    out <== mux.out;
}


/*

*** SegmentMulFix(): template that does a multiplication of a scalar times a fix base. It receives a point in Edwards representation base and a binary input in representing a value k, and calculates the point k * p.
        - Inputs: e[3 * nWindows] -> binary representation of the scalar
                                     requires tag binary
                  base[2] -> input curve point in Edwards representation
        - Outputs: out[2] -> output curve point in Edwards representation
                   dbl[2] -> output curve point in Montgomery representation (to be linked to the next segment)
    
 */


// TODO: We are returning dbl in Montgomery and then transforming it to Edwards to then again transform it to Montgomery here. We can improve this if we expect a value in MOntgomery and only transform outside the first value. If we have a lot of segments we are improving the efficiency

template SegmentMulFix(nWindows) {
    signal input {binary} e[nWindows*3];
    signal input base[2];
    signal output out[2];
    signal output dbl[2];

    var i;
    var j;

    // Convert the base to montgomery

    component e2m = Edwards2Montgomery();
    e2m.in <== base;

    component windows[nWindows];
    component adders[nWindows];
    component cadders[nWindows];

    // In the last step we add an extra doubler so that numbers do not match.
    component dblLast = MontgomeryDouble();

    for (i=0; i<nWindows; i++) {
        windows[i] = WindowMulFix();
        cadders[i] = MontgomeryAdd();
        if (i==0) {
            windows[i].base <== e2m.out;
            cadders[i].in1 <== e2m.out;
        } else {
            windows[i].base <== windows[i-1].out8;
            cadders[i].in1 <== cadders[i-1].out;
        }
        for (j=0; j<3; j++) {
            windows[i].in[j] <== e[3*i+j];
        }
        if (i<nWindows-1) {
            cadders[i].in2 <== windows[i].out8;
        } else {
            dblLast.in <== windows[i].out8;
            cadders[i].in2 <== dblLast.out;
        }
    }

    for (i=0; i<nWindows; i++) {
        adders[i] = MontgomeryAdd();
        if (i==0) {
            adders[i].in1 <== dblLast.out;
        } else {
            adders[i].in1 <== adders[i-1].out;
        }
        adders[i].in2 <== windows[i].out;
    }

    component m2e = Montgomery2Edwards();
    component cm2e = Montgomery2Edwards();

    m2e.in <== adders[nWindows-1].out;
    cm2e.in <== cadders[nWindows-1].out;

    component cAdd = BabyAdd();
    cAdd.x1 <== m2e.out[0];
    cAdd.y1 <== m2e.out[1];
    cAdd.x2 <== -cm2e.out[0];
    cAdd.y2 <== cm2e.out[1];

    cAdd.xout ==> out[0];
    cAdd.yout ==> out[1];

    windows[nWindows-1].out8 ==> dbl;
}

/*

*** EscalarMulFix(): template that does a multiplication of a scalar times a fixed point BASE. It receives a point in Edwards representation BASE and a binary input in representing a value k, and calculates the point k * p.
        - Inputs: e[n] -> binary representation of the scalar
                          requires tag binary
        - Outputs: out[2] -> output curve point in Edwards representation
    
 */
template EscalarMulFix(n, BASE) {
    signal input {binary} e[n];              // Input in binary format
    signal output out[2];           // Point (Twisted format)

    var nsegments = (n-1)\246 +1;       // 249 probably would work. But I'm not sure and for security I keep 246
    var nlastsegment = n - (nsegments-1)*249;

    component segments[nsegments];

    component m2e[nsegments-1];
    component adders[nsegments-1];

    var s;
    var i;
    var nseg;
    var nWindows;
    
    signal {binary} aux_0 <== 0;

    for (s=0; s<nsegments; s++) {

        nseg = (s < nsegments-1) ? 249 : nlastsegment;
        nWindows = ((nseg - 1)\3)+1;

        segments[s] = SegmentMulFix(nWindows);

        for (i=0; i<nseg; i++) {
            segments[s].e[i] <== e[s*249+i];
        }
        
        for (i = nseg; i<nWindows*3; i++) {
        
            segments[s].e[i] <== aux_0;
        }

        if (s==0) {
            segments[s].base <== BASE;
        } else {
            m2e[s-1] = Montgomery2Edwards();
            adders[s-1] = BabyAdd();

            segments[s-1].dbl ==> m2e[s-1].in;
            m2e[s-1].out ==> segments[s].base;

            if (s==1) {
                segments[s-1].out[0] ==> adders[s-1].x1;
                segments[s-1].out[1] ==> adders[s-1].y1;
            } else {
                adders[s-2].xout ==> adders[s-1].x1;
                adders[s-2].yout ==> adders[s-1].y1;
            }
            segments[s].out[0] ==> adders[s-1].x2;
            segments[s].out[1] ==> adders[s-1].y2;
        }
    }
    
    segments[nsegments - 1].dbl ==> _;

    if (nsegments == 1) {
        segments[0].out ==> out;
    } else {
        adders[nsegments-2].xout ==> out[0];
        adders[nsegments-2].yout ==> out[1];
    }
}
