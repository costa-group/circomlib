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

/*

*** RotR(n, r): template that receives an array of n bits and returns the array rotated r positions to the right
 
        - Inputs: in[n] -> array of n bits
                          requires tag binary
        - Output: out[n] -> array of n bits, it takes the value: 
                                out[i] = in[(i + r) % n]
                            satisfies tag binary
        
    Example: RotR(4, 1)([1, 0, 1, 1]) = [0, 1, 1, 1]

*/

template RotR(n, r) {
    signal input {binary} in[n];
    signal output {binary} out[n];

    for (var i=0; i<n; i++) {
        out[i] <== in[ (i+r)%n ];
    }
}
