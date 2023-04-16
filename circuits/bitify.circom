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
include "tags-specifications.circom";


// The templates and functions in this file are general and work for any prime field

// To consult the tags specifications check tags-specifications.circom


/*
*** maxbits(): function that returns the maximum number of bits that we use to represent a number with no overflows in the field
        - Inputs: None
        - Outputs: maximum number of bits that we can use in the field without overflows
        
    
    Example: if we consider the prime p = 11, then maxbits() = 3 as if we consider 4 bits overflows may happen [1, 1, 1, 1] = 15 -> overflows to 4
*/

function maxbits(){
    var n = 1;
    var r = 1;
    while(2 * n > n){
        n = n * 2;
        r = r + 1;
    }
    return r;
}


/*
*** nbits(x): function that returns the number of bits that we need to represent the value x
        - Inputs: x -> field value 
        - Output: number of bits needed to represent x
        
    Example: nbits(7) = 3, nbits(10) = 4

*/

function nbits(a) {
    if (a == 0){
       return 1;
    }
    else{
        var n = 1;
        var r = 0;
    
        while (n-1<a) {
            r++;
            n *= 2;
        }
        if (n < 0){ // in case n > p \ 2 -> we need maxbits() + 1 bits
            return(maxbits() + 1); 
        } else{
            return r;
        }
    }
}


/*
*** Num2Bits(n): template that transforms an input into its binary representation using n bits
        - Inputs: in -> field value
        - Output: out[n] -> binary representation of in using n bits
                            satisfies tag binary
        - Parameter conditions: n <= maxbits() + 1
         
    Example: Num2Bits(3)(7) = [1, 1, 1]
    Note: in case the input in cannot be represented using n bits then the generated system of constraints does not have any solution for that input. 
          For instance, Num2Bits(3)(10) -> no solution
          
*/

template Num2Bits(n){
    signal input in;
    signal output {binary} out[n];
    
    assert(n <= maxbits() + 1);
    
    var lc1=0;
    var e2=1;
    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0; // to ensure binary
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === in; // to ensure that out is the binary representation of in
    
    if (n == maxbits() + 1) { // in this case we need to add extra constraints to ensure uniqueness
        component aliasCheck = AliasCheck();
        out ==> aliasCheck.in;
        
    }

}

/* 

------> equivalent to Num2Bits(maxbits() + 1)

*** Num2Bits_strict(): template that transforms an input into its binary representation using maxbits() + 1  bits
        - Inputs: in -> field value
        - Output: out[n] -> binary representation of in using maxbits() + 1 bits
                  satisfies tag binary
         
    Example: Assuming p = 11, then Num2Bits_strict()(13) = [0, 1, 0, 0]

*/

template Num2Bits_strict() {
    signal input in;
    signal output {binary} out[maxbits() + 1];

    component aliasCheck = AliasCheck();
    component n2b = Num2Bits(maxbits() + 1);
    in ==> n2b.in;

    n2b.out ==> out;
    n2b.out ==> aliasCheck.in;
}

/*

*** Bits2Num(n): template that transforms an input of n bits representing a value x in binary into the decimal representation of x
        - Inputs: in[n] -> binary representation of out using n bits
                           satisfies tag binary
        - Output: out -> value represented by the input
                         satisfies tag maxbit with out.maxbit =  n
        - Parameter conditions: n <= maxbits() + 1?
         
    Example: Bits2Num(3)([1, 0, 1]) = 5
          
*/

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
}

/* 

------> equivalent to Bits2Num(maxbits() + 1)(in)

*** Bits2Num_strict(): template that transforms an input of maxbits() + 1 bits representing a value x in binary into the decimal representation of x
        - Inputs: in[n] -> binary representation of out using maxbits() + 1 bits
                           satisfies tag binary
        - Output: out -> value represented by the input
                         satisfies tag maxbit with out.maxbit =  maxbits() + 1
         
    Example: Assuming p = 11, then Bits2Num_strict()([1, 1, 0, 1]) = 2 (13 mod 11 = 2)

*/

template Bits2Num_strict() {
    signal input {binary} in[maxbits() + 1];
    signal output {maxbit} out;

    out.maxbit = maxbits() + 1;
    
    component b2n = Bits2Num(maxbits() + 1);
    b2n.in <== in;
    b2n.out ==> out;
}

/*
*** Num2BitsNeg(n): template that given an input x returns the binary representation of 2 ** n - x using n bits, in case in == 0 then it returns 0
        - Inputs: in -> field value
        - Output: out[n] -> if in != 0 then binary representation of 2 ** n - in using n bits, else 0
                            satisfies tag binary
        - Parameter conditions: n <= maxbits()
         
    Example: Num2BitsNeg(3)(2) = [0, 1, 1], Num2Bits(3)(8) = [0, 0, 0]
          
*/


template Num2BitsNeg(n){ // Same number of non linear constraints. easier to follow?
    signal input in;
    signal output {binary} out[n];
    
    assert(n <= maxbits()); 
    
    component iszero = IsZero();
    iszero.in <== in;
    
    component n2b = Num2Bits(n);
    n2b.in <== (2 ** n - in) * (1 - iszero.out); // in case in = 0 then 0 else n - in 
    out <== n2b.out;
    
}


template Num2BitsNeg_old(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    component isZero;

    isZero = IsZero();

    var neg = n == 0 ? 0 : 2**n - in;

    for (var i = 0; i<n; i++) {
        out[i] <-- (neg >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * 2**i;
    }

    in ==> isZero.in;



    lc1 + isZero.out * 2**n === 2**n - in;
}
