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

include "compconstant.circom";


template AliasCheck() {

    signal input {binary} in[254];

    component  compConstant = CompConstant(-1);

    for (var i=0; i<254; i++) in[i] ==> compConstant.in[i];

    compConstant.out === 0;
    
    // specification:
    var sum_spec = 0;
    var e2 = 1;
    for(var i = 0; i < 254; i ++){
       sum_spec = sum_spec + in[i] * e2;
       e2 = e2 + e2;
    }
    
    spec_postcondition sum_spec <= 21888242871839275222246405745257275088548364400416034343698204186575808495616;
}
