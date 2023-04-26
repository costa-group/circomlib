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
include "escalarmulfix.circom";

// To consult the tags specifications check tags-specifications.circom


/*
*** BabyAdd(): template that receives two inputs (x1, y1), (x2, y2) representing points of the Baby Jubjub curve in Edwards form and returns the addition of the points (xout, yout)
        - Inputs: x1, y1 -> two field values representing a point of the curve in Edwards form
                  x2, y2 -> two field values representing a point of the curve in Edwards form
        - Outputs: xout, yout -> two field values representing a point of the curve in Edwards form, (xout, yout) = (x1, y1) + (x2, y2)
         
    Example:
    
    tau = d * x1 * x2 * y1 * y3
    
    
                      x1 * y2 + y1 * x2       y1 * y2 - x1 * x2
    [xout, yout] = [ -------------------  , -------------------- ]
                          1 + d * tau            1 - d * tau     
    
*/

template BabyAdd() {
    signal input x1;
    signal input y1;
    signal input x2;
    signal input y2;
    signal output xout;
    signal output yout;
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    signal beta;
    signal gamma;
    signal delta;
    signal tau;

    var a = 168700;
    var d = 168696;

    beta <== x1*y2;
    gamma <== y1*x2;
    delta <== (-a*x1+y1)*(x2 + y2);
    tau <== beta * gamma;

    xout <-- (beta + gamma) / (1+ d*tau);
    (1+ d*tau) * xout === (beta + gamma);

    yout <-- (delta + a*beta - gamma) / (1-d*tau);
    (1-d*tau)*yout === (delta + a*beta - gamma);
}

/*
*** BabyDouble(): template that receives an input (x, y) representing a point of the Baby Jubjub curve in Edwards form and returns the addition of the points (xout, yout)
        - Inputs: x, y -> two field values representing a point of the curve in Edwards form
        - Outputs: xout, yout -> two field values representing a point of the curve in Edwards form. 2 * (x, y) = (xout, yout)
         
    Example: BabyDouble()(x, y) = BabyAdd()(x, y, x, y)
    
*/


template BabyDbl() {
    signal input x;
    signal input y;
    signal output xout;
    signal output yout;
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616); // to ensure that we are using the right prime

    component adder = BabyAdd();
    adder.x1 <== x;
    adder.y1 <== y;
    adder.x2 <== x;
    adder.y2 <== y;

    adder.xout ==> xout;
    adder.yout ==> yout;
}

/*
*** BabyDouble(): template that receives an input (x, y) and checks if it belongs to the Baby Jubjub curve
        - Inputs: x, y -> two field values representing the point the point that we want to check
        - Outputs: None
        
    Example: The set of solutions of BabyDouble()(x, y) are the points of the Baby Jubjub curve
    
*/

template BabyCheck() {
    signal input x;
    signal input y;

    signal x2;
    signal y2;
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    var a = 168700;
    var d = 168696;

    x2 <== x*x;
    y2 <== y*y;

    a*x2 + y2 === 1 + d*x2*y2;
}


/*
*** BabyPbk(): template that receives an input in representing a point of the prime field and returns the point in * P with P being the point of the Baby Jubjub curve 
P = (5299619240641551281634865583518297030282874472190772894086521144482721001553, 16950150798460657717958625567821834550301663161624707787222815936182638968203)
This template is used to extract the public key from the private key.
        - Inputs: in -> field value
        - Outputs: (Ax, Ay) -> two field values representing a point of the curve in Edwards form, in * P = (Ax, Ay)
    
*/

template BabyPbk() {
    signal input  in;
    signal output Ax;
    signal output Ay;
    
    assert(-1 == 21888242871839275222246405745257275088548364400416034343698204186575808495616);

    var BASE8[2] = [
        5299619240641551281634865583518297030282874472190772894086521144482721001553,
        16950150798460657717958625567821834550301663161624707787222815936182638968203
    ];

    component pvkBits = Num2Bits(253);
    pvkBits.in <== in;

    component mulFix = EscalarMulFix(253, BASE8);
    mulFix.e <== pvkBits.out;
    
    Ax  <== mulFix.out[0];
    Ay  <== mulFix.out[1];
}
