pragma circom 2.1.5;
include "../../circuits/bitify.circom";

template Main() {
    signal input in;
    
    component n2b = Num2Bits_strict();
    component b2n = Bits2Num_strict();
    
    n2b.in <== in;
    signal {binary} aux[maxbits() + 1] <== n2b.out;
    
    b2n.in <== aux;
    signal {maxbit} aux2 <== b2n.out;
    
    assert(aux2.maxbit == maxbits() + 1);
    log(aux2);
    in === aux2;
}

component main = Main();
