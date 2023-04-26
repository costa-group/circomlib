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
    Source: https://en.wikipedia.org/wiki/Montgomery_curve

 */
pragma circom 2.1.5;

include "tags-specifications.circom";

// To consult the tags specifications check tags-specifications.circom


/*
*** Edwards2Montgomery(): template that receives an input in representing a point of an elliptic curve in Edwards form and returns the equivalent point in Montgomery form
        - Inputs: in[2] -> array of 2 field values representing a point of the curve in Edwards form
        - Outputs: out[2] -> array of 2 field values representing a point of the curve in Montgomery form
         
    Example: if we consider the input in = [x, y], then the circuit produces the following output [u, v]
    
                1 + y       1 + y
    [u, v] = [ -------  , ---------- ]
                1 - y      (1 - y)x
    
*/

template Edwards2Montgomery() {
    signal input in[2];
    signal output out[2];

    out[0] <-- (1 + in[1]) / (1 - in[1]);
    out[1] <-- out[0] / in[0];


    out[0] * (1-in[1]) === (1 + in[1]);
    out[1] * in[0] === out[0];
}


/*
*** Montgomery2Edwards(): template that receives an input in representing a point of an elliptic curve in Montgomery form and returns the equivalent point in Edwards form
        - Inputs: in[2] -> array of 2 field values representing a point of the curve in Montgomery form
        - Outputs: out[2] -> array of 2 field values representing a point of the curve in Edwards form
         
    Example: if we consider the input in = [u, v], then the circuit produces the following output [x, y]
    
                u    u - 1
    [x, y] = [ ---, ------- ]
                v    u + 1

 */
 
template Montgomery2Edwards() {
    signal input in[2];
    signal output out[2];

    out[0] <-- in[0] / in[1];
    out[1] <-- (in[0] - 1) / (in[0] + 1);

    out[0] * in[1] === in[0];
    out[1] * (in[0] + 1) === in[0] - 1;
}


/*
*** MontgomeryAdd(): template that receives two inputs in1, in2 representing points of the Baby Jubjub curve in Montgomery form and returns the addition of the points
        - Inputs: in1[2] -> array of 2 field values representing a point of the curve in Montgomery form
                  in2[2] -> array of 2 field values representing a point of the curve in Montgomery form
        - Outputs: out[2] -> array of 2 field values representing the point in1 + in2 in Montgomery form
         
    Example: if we consider the inputs in1 = [x1, y1] and in2 = [x2, y2], then the circuit produces the following output [x3, y3]:

             y2 - y1
    lamda = ---------
             x2 - x1

    x3 = B * lamda^2 - A - x1 -x2

    y3 = lamda * ( x1 - x3 ) - y1
    
    where A and B are two constants defined below. 
 */

template MontgomeryAdd() {
    signal input in1[2];
    signal input in2[2];
    signal output out[2];
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616); // to ensure the correct prime

    var a = 168700;
    var d = 168696;

    var A = (2 * (a + d)) / (a - d);
    var B = 4 / (a - d);

    signal lamda;

    lamda <-- (in2[1] - in1[1]) / (in2[0] - in1[0]);
    lamda * (in2[0] - in1[0]) === (in2[1] - in1[1]);

    out[0] <== B*lamda*lamda - A - in1[0] -in2[0];
    out[1] <== lamda * (in1[0] - out[0]) - in1[1];
}


/*
*** MontgomeryDouble(): template that receives an input in1 representing a point of the Baby Jubjub curve in Montgomery form and returns the point 2 * in
        - Inputs: in[2] -> array of 2 field values representing a point of the curve in Montgomery form
        - Outputs: out[2] -> array of 2 field values representing the point 2*in in Montgomery form
         
         
    Example: if we consider the input in = [x1, y1], then the circuit produces the following output [x3, y3]:

    x1_2 = x1*x1

             3*x1_2 + 2*A*x1 + 1
    lamda = ---------------------
                   2*B*y1

    x3 = B * lamda^2 - A - x1 -x1

    y3 = lamda * ( x1 - x3 ) - y1

 */
 
template MontgomeryDouble() {
    signal input in[2];
    signal output out[2];

    var a = 168700;
    var d = 168696;
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    var A = (2 * (a + d)) / (a - d);
    var B = 4 / (a - d);

    signal lamda;
    signal x1_2;

    x1_2 <== in[0] * in[0];

    lamda <-- (3*x1_2 + 2*A*in[0] + 1 ) / (2*B*in[1]);
    lamda * (2*B*in[1]) === (3*x1_2 + 2*A*in[0] + 1 );

    out[0] <== B*lamda*lamda - A - 2*in[0];
    out[1] <== lamda * (in[0] - out[0]) - in[1];
}
