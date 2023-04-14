pragma circom 2.1.5;
include "../../circuits/bitify.circom";
include "../../circuits/comparators.circom";

template Main(n) {
    signal input in;

    component n2b = Num2BitsNeg(n);
    n2b.in <== in;
    signal {binary} aux[n] <== n2b.out;
    
    component iszero = IsZero();
    iszero.in <== in;
    
    component b2n = Bits2Num(n);
    b2n.in <== aux;
    signal {maxbit} aux2 <== b2n.out;
    
    assert(aux2.maxbit == n);
    
    log(2**30);
    log(in);
    log(aux2); 
    2 ** n - in - 2 ** n * iszero.out  === aux2;
}


component main = Main(30);
