pragma circom 2.1.5;
include "../../circuits/bitify.circom";

template Main(n) {
    signal input in;

    component n2b = Num2Bits(n);
    component b2n = Bits2Num(n);
    
    n2b.in <== in;
    signal {binary} aux[n] <== n2b.out;
    
    b2n.in <== aux;
    signal {maxbit} aux2 <== b2n.out;
    
    assert(aux2.maxbit == n);
    in === aux2;
}


component main = Main(30);
