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

// https://github.com/zcash-hackworks/sapling-crypto
// https://github.com/ebfull/bellman


pragma circom 2.1.5;

include "tags-specifications.circom";
include "comparators.circom";

// The templates and functions in this file are general and work for any prime field

// To consult the tags specifications check tags-specifications.circom

/*

*** EscalarProduct(n): template that implements the escalar product of two vectors of n elements 

        - Inputs: in1[n] -> array of n field elements
                  in2[n] -> array of n field elements
        - Output: out -> field element, escalar product of in1 and in2: out = in1[0] * in2[0] + ... + in1[n-1] * in2[n-1]
        
    Example: EscalarProduct(3)([1, 5, 3], [2, 0, 1]) = 5

 */

template EscalarProduct(w) {
    signal input in1[w];
    signal input in2[w];
    signal output out;
    signal aux[w];
    var lc = 0;
    for (var i=0; i<w; i++) {
        aux[i] <== in1[i]*in2[i];
        lc = lc + aux[i];
    }
    out <== lc;
}

/*

*** Decoder(n): template that receives an input and returns a vector out of n bits such that out[inp] = 1 and the rest of the elements are 0
        - Inputs: inp -> field value
        - Output: out[n] -> array of n binary values, for i in 0..n: out[i] = 1 if i = inp, else out[i] = 0 
                            satisfies tag binary
                  success -> binary value, success = w < inp
                             satisfies tag binary   
        
    Example: Decoder(3)(2) = ([0, 0, 1], 1), Decoder(3)(4) = ([0, 0, 0], 0)

 */

template Decoder(w) {
    signal input inp;
    signal output {binary} out[w];
    signal output {binary} success;
    var lc=0;
    
    component checkZero[w];
    for (var i=0; i<w; i++) {
        checkZero[i] = IsZero();
        checkZero[i].in <== inp - i;
        out[i] <== checkZero[i].out;
        lc = lc + out[i];
    }
    lc ==> success;
}

/*

*** Decoder_strict(n): template that receives an input and returns a vector out of n bits such that out[inp] = 1 and the rest of the elements are 0. In case inp >= n the template fails and does not accept any witness
        - Inputs: inp -> field value
        - Output: out[n] -> array of n binary values, for i in 0..n: out[i] = 1 if i = inp, else out[i] = 0 
                            satisfies tag binary
        
    Example: Decoder_strict(3)(2) = [0, 0, 1], Decoder_strict(2)(4) no solution
    Note: in case inp >= w the R1CS system of constraints does not have any solution

 */

template Decoder_strict(w) {
    signal input inp;
    signal output {binary} out[w];
    var lc=0;

    for (var i=0; i<w; i++) {
        out[i] <-- (inp == i) ? 1 : 0;
        out[i] * (inp-i) === 0;
        lc = lc + out[i];
    }

    lc === 1;
}

/*

*** Multiplexer(wIn, nIn): template that implements a multiplexer nIn-to-1 between two inputs of wIn elements
    - If sel == 0 then out = inp[0]
    - If sel == 1 then out = inp[1]
    ...
    - If sel == nIn - 1 then out = inp[nIn - 1]

        - Inputs: sel -> field value
                  inp[nIn][wIn] -> nIn arrays of wIn elements that correspond to the inputs of the mux: inp[0] => first input, inp[1] => second input, ...
        - Output: out[n] -> array of n elements, it takes the value inp[0] if sel == 0, inp[1] if sel == 1, ..., inp[nIn-1] if sel == nIn - 1 
        
    Example: Multiplexer(2, 3)([[1, 2], [2, 3], [2, 4]], 2) = [2, 4]

 */

template Multiplexer(wIn, nIn) {
    signal input inp[nIn][wIn];
    signal input sel;
    signal output out[wIn];
    
    component dec = Decoder_strict(nIn);
    dec.inp <== sel;   
    
    component ep[wIn];

    for (var j=0; j<wIn; j++) {
        ep[j] = EscalarProduct(nIn);
        for (var k=0; k<nIn; k++) {
            inp[k][j] ==> ep[j].in1[k];
        }
        ep[j].in2 <== dec.out;
        ep[j].out ==> out[j];
    }
}
