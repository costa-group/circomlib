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

/* Ch

000 0
001 1
010 0
011 1
100 0
101 0
110 1
111 1

out = a&b ^ (!a)&c =>

out = a*(b-c) + c

*/
pragma circom 2.0.0;


template Ch_t_aux(){
   signal input {binary} a;
   signal input {binary} b;
   signal input {binary} c;
   signal output {binary} out;
   
   out <== a * (b-c) + c;
   spec_postcondition (a == 0 && b == 0 && c == 0) => (out == 0);
   spec_postcondition (a == 0 && b == 0 && c == 1) => (out == 1);
   spec_postcondition (a == 0 && b == 1 && c == 0) => (out == 0);
   spec_postcondition (a == 0 && b == 1 && c == 1) => (out == 1);
   spec_postcondition (a == 1 && b == 0 && c == 0) => (out == 0);
   spec_postcondition (a == 1 && b == 0 && c == 1) => (out == 0);
   spec_postcondition (a == 1 && b == 1 && c == 0) => (out == 1);
   spec_postcondition (a == 1 && b == 1 && c == 1) => (out == 1);
}

template Ch_t(n) {
    signal input {binary} a[n];
    signal input {binary} b[n];
    signal input {binary} c[n];
    signal output {binary} out[n];

    for (var k=0; k<n; k++) {
        out[k] <== Ch_t_aux()(a[k], b[k], c[k]);
        spec_postcondition (a[k] == 0 && b[k] == 0 && c[k] == 0) => (out[k] == 0);
        spec_postcondition (a[k] == 0 && b[k] == 0 && c[k] == 1) => (out[k] == 1);
        spec_postcondition (a[k] == 0 && b[k] == 1 && c[k] == 0) => (out[k] == 0);
        spec_postcondition (a[k] == 0 && b[k] == 1 && c[k] == 1) => (out[k] == 1);
        spec_postcondition (a[k] == 1 && b[k] == 0 && c[k] == 0) => (out[k] == 0);
        spec_postcondition (a[k] == 1 && b[k] == 0 && c[k] == 1) => (out[k] == 0);
        spec_postcondition (a[k] == 1 && b[k] == 1 && c[k] == 0) => (out[k] == 1);
        spec_postcondition (a[k] == 1 && b[k] == 1 && c[k] == 1) => (out[k] == 1);
    }
    
}
