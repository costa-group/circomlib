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

/* Xor3 function for sha256

out = a ^ b ^ c  =>

out = a+b+c - 2*a*b - 2*a*c - 2*b*c + 4*a*b*c   =>

out = a*( 1 - 2*b - 2*c + 4*b*c ) + b + c - 2*b*c =>

mid = b*c
out = a*( 1 - 2*b -2*c + 4*mid ) + b + c - 2 * mid

       - Inputs: a[n], b[n], c[n] -> satisfy tag binary
        - Outputs: out[n] -> satisfies tag binary

        Example: RotR(4,2)([1,0,0,0]) = [0,0,1,0]
*/

pragma circom 2.0.0;

template Xor3_simple(){
    signal input {binary} a;
    signal input {binary} b;
    signal input {binary} c;
    signal output {binary} out;
    signal mid;
    mid <== b*c;
    out <== a * (1 -2*b  -2*c +4*mid) + b + c -2*mid;    
}

template Xor3(n) {
    signal input {binary} a[n];
    signal input {binary} b[n];
    signal input {binary} c[n];
    signal output {binary} out[n];

    for (var k=0; k<n; k++) {
        out[k] <== Xor3_simple()(a[k],b[k],c[k]);
    }
}