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

include "comparators.circom";
include "aliascheck.circom";


function nbits(a) {
    var n = 1;
    var r = 0;
    while (n-1<a) {
        r++;
        n *= 2;
    }
    return r;
}

template Num2Bits(n) {
    signal input in;
    signal output {binary} out[n];
    var lc1=0;

    var e2=1;
    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        //spec_postcondition out[i] == ((in >> i) % 2);
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }
    
    lc1 === in;
    spec_postcondition lc1 == in;
}

template Num2Bits_strict() {
    signal input in;
    signal output {binary} out[254];
    
    var lc1=0;
    var e2=1;
    for (var i = 0; i<254; i++) {
        out[i] <-- (in >> i) & 1;
        //spec_postcondition out[i] == ((in >> i) % 2);
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }
    lc1 === in;

    AliasCheck()(out);
    
    // to generate the postconditions:
    
    spec_postcondition lc1 == in;
}

template Bits2Num(n) {
    signal input {binary} in[n];
    signal output {maxbit} out;
    var lc1=0;
    var e2 = 1;
    for (var i = 0; i<n; i++) {
        lc1 += in[i] * e2;
        e2 = e2 + e2;
    }
    out.maxbit = n;
    lc1 ==> out;
    
    spec_postcondition out == lc1;
}

template Bits2Num_strict() {
    signal input {binary} in[254];
    signal output {maxbit} out;

    // Option 1: adds the constraints in every situation
    //AliasCheck()(in);
    


    var lc1 = 0;
    var e2 = 1;
    for (var i = 0; i<254; i++) {
        lc1 += in[i] * e2;
        e2 = e2 + e2;
    }
    out.maxbit = 254;
    lc1 ==> out;

    // Option2: only when we can assume that the input is a valid binary representation
    spec_precondition lc1 <= 21888242871839275222246405745257275088548364400416034343698204186575808495616;
    
    spec_postcondition out == lc1;
}

template Num2BitsNeg(n) {
    signal input in;
    signal output {binary} out[n];
    
    signal output nout;
    var lc1=0;

    component isZero;

    isZero = IsZero();

    var neg = n == 0 ? 0 : 2**n - in;

    for (var i = 0; i<n; i++) {
        out[i] <-- (neg >> i) & 1;
        //spec_postcondition out[i] == ((neg >> i) % 2);
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * 2**i;
    }

    in ==> isZero.in;

    nout <== isZero.out;

    lc1 + isZero.out * 2**n === 2**n - in;
    
    spec_postcondition ((in == 0) => (lc1 == 0)) && (!(in == 0) => (2 ** n - in == lc1));
    spec_postcondition nout == (in == 0);
}
