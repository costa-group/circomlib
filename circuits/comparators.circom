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

include "bitify.circom";
include "gates.circom";



// The templates and functions in this file are general and work for any prime field

// To consult the tags specifications check tags-specifications.circom


/*
*** IsNegative(): template that receives an input in representing a field value and checks if the value is positive or negative. We consider a number positive in case in <= p \ 2 and negative otherwise 
        - Inputs: in -> field value
        - Outputs: sign -> 0 in case in <= prime \ 2, 1 otherwise
                           satisfies tag binary
         
    Example: in case we are working in the prime field with p = 11, then IsNegative()(9) = 1 as 9 > 5, IsNegative()(4) = 0 as 4 <= 5
          
*/

template IsNegative() {
    // check if a signal is negative in circom sense
    signal input in;
    signal output {binary} out;
    var max = -1 >> 1;
    out <== CompConstant(max)(Num2Bits(maxbits() + 1)(in)); // maxbits() + 1 + 2 * 
}

/*
*** IsNegativeBounded(): template that receives an input in representing a field value and returns if the value is positive or negative. We consider a number positive in case in <= p \ 2 and negative otherwise, assuming that the absolute value of the input signal is bounded by in.max_abs: -in.max_abs <= in <= in.max_abs.
        - Inputs: in -> field value such that -in.max_abs <= in <= in.max_abs
                        requires tag max_abs
        - Outputs: sign -> 0 in case in <= prime \ 2, 1 otherwise
                           satisfies tag binary
         
    Example: in case we are working in the prime field with p = 11, the template IsNegativeBounded() with in.max_abs = 3 can handle numbers from -3 to 3 only using 3 non-linear constraints
          
*/

template IsNegativeBounded(){
    signal input {max_abs} in;
    signal output {binary} out;
    
    signal aux <== in + in.max_abs;
    out <== LessThan(nbits(2 * in.max_abs))([aux, in.max_abs]);
}

/*
*** IsZero(): template that receives an input in representing a field value and returns 1 if the input value is zero, 0 otherwise.
        - Inputs: in -> field value
        - Outputs: out -> in == 0
                          satisfies tag binary
         
    Example: IsZero()(5) = 0, IsZero()(0) = 0
          
*/

template IsZero() {
    signal input in;
    signal output {binary} out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
*** IsEqual(): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] == in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] == in[1]
                          satisfies tag binary
         
    Example: IsEqual()([5, 2]) = 0, IsZero()([2, 2]) = 0
          
*/


template IsEqual() {
    signal input in[2];
    signal output {binary} out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
*** ForceEqualIfEnabled(): template that receives two inputs in[0] and in[1] representing field values and checks that in[0] == in[1] in case enabled == 1
        - Inputs: in[2] -> array of 2 field values
                  enabled -> binary value
                             requires tag binary
        - Outputs: None
         
    Example: ForceEqualIfEnabled()([5, 2], 1) is not satisfiable as in[0] != in[1] and enabled = 1
          
*/

template ForceEqualIfEnabled() {
    signal input {binary} enabled;
    signal input in[2];

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    (1 - isz.out)*enabled === 0;
}

/*
*** LessThanBounded(): template that receives two inputs in[0] and in[1] bounded by 2**in.maxbit representing field values and returns 1 if in[0] < in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
                           requires tag maxbit
        - Outputs: out -> in[0] < in[1]
                          satisfies tag binary
         
    Example: LessThanBounded()([5, 2]) = 0, LessThanBounded()([1, 2]) = 1
          
*/

template LessThanBounded() {
    signal input {maxbit} in[2];
    signal output {binary} out;
    
    if(in.maxbit <= maxbits() - 1){
    	component n2b = Num2Bits(in.maxbit + 1);
    	n2b.in <== in[0]+ (1<<in.maxbit) - in[1];
    	out <== 1-n2b.out[in.maxbit];    
    	for (var i = 0; i < in.maxbit; i++){
       	_ <== n2b.out[i];
    	}
    } else{
        component lets = LessThan_strict();
        lets.in <== in;
        out <== lets.out;
    }

}

/*
*** LessThan_strict(): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] < in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] < in[1]
                          satisfies tag binary
         
    Example: LessThan_strict()([5, 2]) = 0, LessThan_strict()([1, 2]) = 1
    
    Note: accepts inputs of all sizes. It considers the numbers in (p\2, p-1) as negative values  
          
*/

template LessThan_strict() {
    signal input in[2];
    signal output {binary} out;
    
    component isn = IsNegative();
    isn.in <== in[0] - in[1];
    out <== isn.out;
}

/*

-------> deprecated

*** LessThan(n): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] < in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] < in[1]
                          satisfies tag binary
         
    Example: LessThan()([5, 2]) = 0, LessThan()([1, 2]) = 1
    
    Note: in case in[0] or in[1] >= 2**n the template could present unexpected behaviours
          
*/


template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output {binary} out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];
    for (var i = 0; i < n; i++){
       _ <== n2b.out[i];
    }
}


/*
*** GreaterThanBounded(): template that receives two inputs in[0] and in[1] bounded by 2**in.maxbit representing field values and returns 1 if in[0] > in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
                           requires tag maxbit
        - Outputs: out -> in[0] > in[1]
                          satisfies tag binary
         
    Example: GreaterThanBounded()([5, 2]) = 1, GreaterThanBounded()([2, 2]) = 0
          
*/

template GreaterThanBounded() {
    signal input {maxbit} in[2];
    signal output {binary} out;

    component lt = LessThanBounded();
    lt.in[0] <== in[1];
    lt.in[1] <== in[0];
    lt.out ==> out;
}


/*
*** GreaterThan_strict(): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] > in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] > in[1]
                          satisfies tag binary
         
    Example: GreaterThan_strict()([5, 2]) = 1, GreaterThan_strict()([1, 2]) = 0
    
    Note: accepts inputs of all sizes. It considers the numbers in (p\2, p-1) as negative values     
*/

template GreaterThan_strict() {
    signal input in[2];
    signal output {binary} out;

    component lt = LessThan_strict();
    lt.in[0] <== in[1];
    lt.in[1] <== in[0];
    lt.out ==> out;
    
}


/*

-------> deprecated

*** GreaterThan(n): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] > in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] > in[1]
                          satisfies tag binary
         
    Example: GreaterThan()([5, 2]) = 1, GreaterThan()([2, 2]) = 0
    
    Note: in case in[0] or in[1] >= 2**n the template could present unexpected behaviours
          
*/

template GreaterThan(n) {
    signal input in[2];
    signal output {binary} out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0];
    lt.out ==> out;
}

/*
*** LessEqThanBounded(): template that receives two inputs in[0] and in[1] bounded by 2**in.maxbit representing field values and returns 1 if in[0] <= in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
                           requires tag maxbit
        - Outputs: out -> in[0] <= in[1]
                          satisfies tag binary
         
    Example: LessEqThanBounded()([5, 2]) = 0, LessEqThanBounded()([2, 2]) = 1
          
*/

template LessEqThanBounded() {
    signal input {maxbit} in[2];
    signal output {binary} out;

    component gt = GreaterThanBounded();
    gt.in <== in;
    
    component nt = NOT();
    nt.in <== gt.out;
    nt.out ==> out;
}


/*
*** LessEqThan_strict(): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] <= in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] <= in[1]
                          satisfies tag binary
         
    Example: LessEqThan_strict()([5, 2]) = 0, LessEqThan_strict()([1, 2]) = 1
    
    Note: accepts inputs of all sizes. It considers the numbers in (p\2, p-1) as negative values     
*/

template LessEqThan_strict() {
    signal input in[2];
    signal output {binary} out;

    NOT()(GreaterThan_strict()(in)) ==> out;
}


/*

-------> deprecated

*** LessEqThan(n): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] <= in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] <= in[1]
                          satisfies tag binary
         
    Example: LessEqThan()([5, 2]) = 0, LessEqThan()([2, 2]) = 1
    
    Note: in case in[0] or in[1] >= 2**n the template could present unexpected behaviours
          
*/

template LessEqThan(n) {
    signal input in[2];
    signal output {binary} out;

    component gt = GreaterThan(n);
    gt.in <== in;
    
    component nt = NOT();
    nt.in <== gt.out;
    nt.out ==> out;
}



/*
*** GreaterEqThanBounded(): template that receives two inputs in[0] and in[1] bounded by 2**in.maxbit representing field values and returns 1 if in[0] >= in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
                           requires tag maxbit
        - Outputs: out -> in[0] >= in[1]
                          satisfies tag binary
         
    Example: GreaterEqThanBounded()([5, 2]) = 1, GreaterEqThanBounded()([2, 2]) = 1
          
*/

template GreaterEqThanBounded() {
    signal input {maxbit} in[2];
    signal output {binary} out;

    component gt = LessThanBounded();
    gt.in <== in;
    
    component nt = NOT();
    nt.in <== gt.out;
    nt.out ==> out;
}


/*
*** GreaterEqThan_strict(): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] >= in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] >= in[1]
                          satisfies tag binary
         
    Example: GreaterEqThan_strict()([5, 2]) = 1, GreaterEqThan_strict()([1, 2]) = 0
    
    Note: accepts inputs of all sizes. It considers the numbers in (p\2, p-1) as negative values     
*/

template GreaterEqThan_strict() {
    signal input in[2];
    signal output {binary} out;

    NOT()(LessThan_strict()(in)) ==> out;
}


/*

-------> deprecated

*** GreaterEqThan(n): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] >= in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] >= in[1]
                          satisfies tag binary
         
    Example: GraeEqThan()([5, 2]) = 1, GreaterEqThan()([2, 2]) = 1
    
    Note: in case in[0] or in[1] >= 2**n the template could present unexpected behaviours
          
*/

template GreaterEqThan(n) {
    signal input in[2];
    signal output {binary} out;

    component gt = LessThan(n);
    gt.in <== in;
    
    component nt = NOT();
    nt.in <== gt.out;
    nt.out ==> out;
}


