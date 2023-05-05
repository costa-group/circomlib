pragma circom 2.1.5;

include "../../circuits/pointbits.circom";


template Main() {
    signal input in[2];

    var i;

    component p2b = Point2Bits_Strict();
    component b2p = Bits2Point_Strict();

    p2b.in <== in;
    b2p.in <== p2b.out;

    b2p.out === in;
}

component main = Main();
