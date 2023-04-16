pragma circom 2.0.0;

include "../../circuits/bitify.circom";
include "../../circuits/binsum.circom";

template A() {
    signal input a; //private
    signal input b;
    signal output out;

    var i;

    component n2ba = Num2Bits(16);
    component n2bb = Num2Bits(16);
    component sub = BinSum(16, 2);
    component b2n = Bits2Num(17);

    n2ba.in <== a;
    n2bb.in <== b;
    
    sub.in[0] <== n2ba.out;
    sub.in[1] <== n2bb.out;


    b2n.in <== sub.out;

    out <== b2n.out;
}

component main = A();
