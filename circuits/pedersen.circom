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
include "mux3.circom";
include "babyjub.circom";
include "tags-specifications.circom";


// To consult the tags specifications check tags-specifications.circom

/*

*** Window4(): template that given a point in Montgomery representation base and a binary input in, calculates:
        out = base + base*in[0] + 2*base*in[1] + 4*base*in[2] in case in[3] == 0, in case in[3] == 1 then it negates out[1]
        
        out4 = 4*base

    This circuit is used in order to perform the Pedersen protocol on an input in.
        - Inputs: in[4] -> binary value
                         requires tag binary
                  base[2] -> input curve point in Montgomery representation
        - Outputs: out[2] -> output curve point in Montgomery representation
                   out8[2] -> output curve point in Montgomery representation
    
 */
template Window4() {
    signal input {binary}in[4];
    signal input base[2];
    signal output out[2];
    signal output out8[2];   // Returns 8*Base (To be linked)
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    component mux = MultiMux3(2);

    mux.s[0] <== in[0];
    mux.s[1] <== in[1];
    mux.s[2] <== in[2];

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

    out[0] <== mux.out[0];
    out[1] <== - mux.out[1]*2*in[3] + mux.out[1];  // Negate y if in[3] is one
}


/*

*** Segment(nWindows):template used to perform a segment of the multiplications needed to perform a the Pedersen protocol. 
        - Inputs: in[4 * nWindows] -> binary representation of the scalar
                                      requires tag binary
                  base[2] -> input curve point in Edwards representation
        - Outputs: out[2] -> output curve point in Edwards representation
    
 */


// TODO: We are returning dbl in Montgomery and then transforming it to Edwards to then again transform it to Montgomery here. We can improve this if we expect a value in MOntgomery and only transform outside the first value. If we have a lot of segments we are improving the efficiency

// TODO: revisar, la ultima window no la usamos en el caso en que nWindows > 1 --> bug o podríamos quitarla?

template Segment(nWindows) {
    signal input {binary} in[nWindows*4];
    signal input base[2];
    signal output out[2];
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    var i;
    var j;

    // Convert the base to montgomery

    component e2m = Edwards2Montgomery();
    e2m.in <== base;

    component windows[nWindows];
    component doublers1[nWindows-1];
    component doublers2[nWindows-1];
    component adders[nWindows-1];
    for (i=0; i<nWindows; i++) {
        windows[i] = Window4();
        for (j=0; j<4; j++) {
            windows[i].in[j] <== in[4*i+j];
        }
        if (i==0) {
            windows[i].base <== e2m.out;
        } else {
            doublers1[i-1] = MontgomeryDouble();
            doublers2[i-1] = MontgomeryDouble();
            doublers1[i-1].in <== windows[i-1].out8;
            doublers2[i-1].in <== doublers1[i-1].out;

            windows[i].base <== doublers2[i-1].out;

            adders[i-1] = MontgomeryAdd();
            if (i==1) {
                adders[i-1].in1 <== windows[0].out;
            } else {
                adders[i-1].in1 <== adders[i-2].out;
            }
            adders[i-1].in2 <== windows[i].out;
        }
    }

    component m2e = Montgomery2Edwards();

    if (nWindows > 1) {
        m2e.in <== adders[nWindows-2].out;
    } else {
        m2e.in <== windows[0].out;
    }

    out <== m2e.out;
}


/*

*** Pedersen(n): template that performs the Pedersen protocol on the input in, that is the binary representation of a value x using n bits. It calculates the output point of the protocol out in Edwards representation
        - Inputs: in[n] -> binary representation of the scalar
                          requires tag binary
        - Outputs: out[2] -> output curve point in Edwards representation
    
 */

template Pedersen(n) {
    signal input {binary} in[n];
    signal output out[2];

    var BASE[10][2] = [
        [10457101036533406547632367118273992217979173478358440826365724437999023779287,19824078218392094440610104313265183977899662750282163392862422243483260492317],
        [2671756056509184035029146175565761955751135805354291559563293617232983272177,2663205510731142763556352975002641716101654201788071096152948830924149045094],
        [5802099305472655231388284418920769829666717045250560929368476121199858275951,5980429700218124965372158798884772646841287887664001482443826541541529227896],
        [7107336197374528537877327281242680114152313102022415488494307685842428166594,2857869773864086953506483169737724679646433914307247183624878062391496185654],
        [20265828622013100949498132415626198973119240347465898028410217039057588424236,1160461593266035632937973507065134938065359936056410650153315956301179689506],
        [1487999857809287756929114517587739322941449154962237464737694709326309567994,14017256862867289575056460215526364897734808720610101650676790868051368668003],
        [14618644331049802168996997831720384953259095788558646464435263343433563860015,13115243279999696210147231297848654998887864576952244320558158620692603342236],
        [6814338563135591367010655964669793483652536871717891893032616415581401894627,13660303521961041205824633772157003587453809761793065294055279768121314853695],
        [3571615583211663069428808372184817973703476260057504149923239576077102575715,11981351099832644138306422070127357074117642951423551606012551622164230222506],
        [18597552580465440374022635246985743886550544261632147935254624835147509493269,6753322320275422086923032033899357299485124665258735666995435957890214041481]

    ];
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    var nSegments = ((n-1)\200)+1;

    component segments[nSegments];

    var i;
    var j;
    var nBits;
    var nWindows;
    
    signal {binary} aux_0 <== 0;
    for (i=0; i<nSegments; i++) {
        nBits = (i == (nSegments-1)) ? n - (nSegments-1)*200 : 200;
        nWindows = ((nBits - 1)\4)+1;
        segments[i] = Segment(nWindows);
        segments[i].base <== BASE[i];
        for (j = 0; j<nBits; j++) {
            segments[i].in[j] <== in[i*200+j];
        }
        // Fill padding bits
        for (j = nBits; j < nWindows*4; j++) {
            segments[i].in[j] <== aux_0;
        }
    }

    component adders[nSegments-1];

    for (i=0; i<nSegments-1; i++) {
        adders[i] = BabyAdd();
        if (i==0) {
            adders[i].x1 <== segments[0].out[0];
            adders[i].y1 <== segments[0].out[1];
            adders[i].x2 <== segments[1].out[0];
            adders[i].y2 <== segments[1].out[1];
        } else {
            adders[i].x1 <== adders[i-1].xout;
            adders[i].y1 <== adders[i-1].yout;
            adders[i].x2 <== segments[i+1].out[0];
            adders[i].y2 <== segments[i+1].out[1];
        }
    }


    if (nSegments>1) {
        out[0] <== adders[nSegments-2].xout;
        out[1] <== adders[nSegments-2].yout;
    } else {
        out[0] <== segments[0].out[0];
        out[1] <== segments[0].out[1];
    }
}

