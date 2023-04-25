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
include "compconstant.circom";
include "tags-specifications.circom";


// The templates and functions in this file are general and work for any prime field

// To consult the tags specifications check tags-specifications.circom


/*
*** Sign(): template that receives an input in representing a value in binary using maxbits() + 1 bits and checks if the value is positive or negative. We consider a number positive in case in <= p \ 2 and negative otherwise 
        - Inputs: in[maxbits() + 1] -> array of maxbits() bits
                                       requires tag binary
        - Outputs: sign -> 0 in case in <= prime \ 2, 1 otherwise
                           satisfies tag binary
         
    Example: in case we are working in the prime field with p = 11, then Sign()([1, 0, 0, 1]) = 1 as 9 > 5, Sign()([0, 0, 1, 0]) = 0 as 4 <= 5
          
*/

template Sign() {
    signal input {binary} in[maxbits() + 1];
    signal output {binary} sign;

    component comp = CompConstant(- 1 \ 2);

    comp.in <== in;
    sign <== comp.out;
}

