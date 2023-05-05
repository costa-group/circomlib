pragma circom 2.1.5;

include "../../circuits/pedersen.circom";
include "../../circuits/bitify.circom";


template Main() {
    signal input in;
    signal output out[2];

    component pedersen = Pedersen(256);

    component n2b;
    n2b = Num2Bits(253);

    var i;

    in ==> n2b.in;

    for  (i=0; i<253; i++) {
        pedersen.in[i] <== n2b.out[i];
    }
    signal {binary} aux_0 <== 0;
    for (i=253; i<256; i++) {
        pedersen.in[i] <== aux_0;
    }

    pedersen.out ==> out;
}

component main = Main();


