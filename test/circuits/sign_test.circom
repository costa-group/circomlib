pragma circom 2.0.0;

include "../../circuits/sign.circom";

template A(){
    signal input in;
    signal aux[maxbits() + 1] <== Num2Bits(maxbits() + 1)(in);
    signal output out <== Sign()(aux);

}

component main = A();
