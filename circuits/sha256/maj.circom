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

/* Maj function for sha256

out = a&b ^ a&c ^ b&c  =>

out = a*b   +  a*c  +  b*c  -  2*a*b*c  =>

out = a*( b + c - 2*b*c ) + b*c =>

mid = b*c
out = a*( b + c - 2*mid ) + mid

*/
pragma circom 2.0.0;

template Maj_t_simple() {
    signal input {binary} a;
    signal input {binary} b;
    signal input {binary} c;
    signal output {binary} out;
    signal mid;
    mid <== b*c;
    out <== a * (b+c-2*mid) + mid;
}


template Maj_t(n) {
    signal input {binary} a[n];
    signal input {binary} b[n];
    signal input {binary} c[n];
    signal output {binary} out[n];

    for (var k=0; k<n; k++) {
        out[k] <== Maj_t_simple()(a[k],b[k],c[k]);
    }
}
