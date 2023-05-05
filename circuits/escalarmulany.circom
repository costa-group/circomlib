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

include "montgomery.circom";
include "babyjub.circom";
include "comparators.circom";
include "mux1.circom";
include "tags-specifications.circom";


// To consult the tags specifications check tags-specifications.circom

/*

*** BitElementMulAny(): template that receives three inputs: sel representing a bit, and two points of the elliptic curve in Montgomery form dblIn and addIn, and returns the points in Montgomery form dblOut and addOut according to the scheme below. This circuit is used in order to multiply a point of the BabyJub curve by a escalar (k * p with p in the curve). 
        - Inputs: sel -> binary value
                         requires tag binary
                  dblIn[2] -> input curve point in Montgomery representation
                  addIn[2] -> input curve point in Montgomery representation
        - Outputs: dblOut[2] -> output curve point in Montgomery representation
                   addOut[2] -> output curve point in Montgomery representation

ADD SCHEME

*/


template BitElementMulAny() {
    signal input {binary} sel;
    signal input dblIn[2];
    signal input addIn[2];
    signal output dblOut[2];
    signal output addOut[2];
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    component doubler = MontgomeryDouble();
    component adder = MontgomeryAdd();
    component selector = MultiMux1(2);


    sel ==> selector.s;

    dblIn ==> doubler.in;

    doubler.out ==> adder.in1;
    addIn ==> adder.in2;

    addIn[0] ==> selector.c[0][0];
    addIn[1] ==> selector.c[1][0];
    adder.out[0] ==> selector.c[0][1];
    adder.out[1] ==> selector.c[1][1];

    doubler.out ==> dblOut;
    selector.out ==> addOut;
}

/*

*** SegmentMulAny(n): template that receives two inputs p[2] and e[n] representing a point of BabyJub curve in its Edwards representation and the binary representation of a field value k respectively, and returns the value out according to the scheme below. This circuit is used in order to multiply a point of the BabyJub curve by a escalar (k * p with p in the curve). 
        - Inputs: e[n] -> binary representation of k
                           requires tag binary
                  p[2] -> input curve point in Edwards representation
        - Outputs: out[2] -> output curve point in Edwards representation

ADD SCHEME

*/

template SegmentMulAny(n) {
    signal input {binary} e[n];
    signal input p[2];
    signal output out[2];
    signal output dbl[2];
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    component bits[n-1];

    component e2m = Edwards2Montgomery();

    p ==> e2m.in;


    var i;

    bits[0] = BitElementMulAny();
    e2m.out ==> bits[0].dblIn;
    e2m.out ==> bits[0].addIn;
    e[1] ==> bits[0].sel;

    for (i=1; i<n-1; i++) {
        bits[i] = BitElementMulAny();
        bits[i-1].dblOut ==> bits[i].dblIn;
        bits[i-1].addOut ==> bits[i].addIn;
        e[i+1] ==> bits[i].sel;
    }

    bits[n-2].dblOut ==> dbl;

    component m2e = Montgomery2Edwards();

    bits[n-2].addOut ==> m2e.in;

    component eadder = BabyAdd();

    m2e.out[0] ==> eadder.x1;
    m2e.out[1] ==> eadder.y1;
    -p[0] ==> eadder.x2;
    p[1] ==> eadder.y2;

    component lastSel = MultiMux1(2);

    e[0] ==> lastSel.s;
    eadder.xout ==> lastSel.c[0][0];
    eadder.yout ==> lastSel.c[1][0];
    m2e.out[0] ==> lastSel.c[0][1];
    m2e.out[1] ==> lastSel.c[1][1];

    lastSel.out ==> out;
}

/*

*** EscalarMulAny(n): template that receives two inputs p[2] and e[n] representing a point of BabyJub curve in its Edwards representation and the binary representation of a field value k respectively, and returns the value out according to the scheme below. This circuit is used in order to multiply a point of the BabyJub curve by a escalar (k * p with p in the curve). The input e is the binary representation of the value k and p is the point of the curve.
        - Inputs: e[n] -> binary representation of k
                           requires tag binary
                  p[2] -> input curve point to be multiplied in Edwards representation
        - Outputs: out[2] -> output curve point k * p in Edwards representation

     Note: This function assumes that p is in the subgroup and it is different to 0

ADD SCHEME

*/

template EscalarMulAny(n) {
    signal input {binary} e[n];              // Input in binary format
    signal input p[2];              // Point (Twisted format)
    signal output out[2];           // Point (Twisted format)
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    var nsegments = (n-1)\148 +1;
    var nlastsegment = n - (nsegments-1)*148;

    component segments[nsegments];
    component doublers[nsegments-1];
    component m2e[nsegments-1];
    component adders[nsegments-1];
    component zeropoint = IsZero();
    zeropoint.in <== p[0];

    var s;
    var i;
    var nseg;

    for (s=0; s<nsegments; s++) {

        nseg = (s < nsegments-1) ? 148 : nlastsegment;

        segments[s] = SegmentMulAny(nseg);

        for (i=0; i<nseg; i++) {
            e[s*148+i] ==> segments[s].e[i];
        }

        if (s==0) {
            // force G8 point if input point is zero
            segments[s].p[0] <== p[0] + (5299619240641551281634865583518297030282874472190772894086521144482721001553 - p[0])*zeropoint.out;
            segments[s].p[1] <== p[1] + (16950150798460657717958625567821834550301663161624707787222815936182638968203 - p[1])*zeropoint.out;
        } else {
            doublers[s-1] = MontgomeryDouble();
            m2e[s-1] = Montgomery2Edwards();
            adders[s-1] = BabyAdd();
            segments[s-1].dbl ==> doublers[s-1].in;

            doublers[s-1].out ==> m2e[s-1].in;

            m2e[s-1].out ==> segments[s].p;

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
        segments[0].out[0]*(1-zeropoint.out) ==> out[0];
        segments[0].out[1]+(1-segments[0].out[1])*zeropoint.out ==> out[1];
        
    } else {
        adders[nsegments-2].xout*(1-zeropoint.out) ==> out[0];
        adders[nsegments-2].yout+(1-adders[nsegments-2].yout)*zeropoint.out ==> out[1];
    }
}
