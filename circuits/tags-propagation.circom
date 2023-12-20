pragma circom 2.1.5;

include "comparators.circom";

template BinaryToMaxbit(){
    signal input {binary} in;
    signal output {maxbit, binary} out;
    
    out.maxbit = 1;
    out <== in;
}

template BinaryToMaxvalue(){
    signal input {binary} in;
    signal output {max, binary} out;
    
    out.max = 1;
    out <== in;
}

template MaxbitToBinary(){
    signal input {maxbit} in;
    signal output {binary, maxbit} out;
    
    assert(in.maxbit <= 1);
    out <== in;
}

template MaxbitToMaxvalue(){
    signal input {maxbit} in;
    signal output {max, maxbit} out;
    
    assert(out.maxbit <= 252);
    
    out.max = 2 ** in.maxbit - 1;
    out <== in;
}

template MaxvalueToBinary(){
    signal input {max} in;
    signal output {binary, max} out;
    
    assert(in.max <= 1);
    out <== in;
}

template MaxvalueToMaxbit(){
    signal input {max} in;
    signal output {maxbit, max} out;
    
    out.maxbit = nbits(in.max);
    out <== in;
}

template RelaxMaxbit(n){
    signal input {maxbit} in;
    signal output {maxbit} out;
    
    assert(out.maxbit <= n);
    
    out.maxbit = n;
    out <== in;
}

template RelaxMaxvalue(n){
    signal input {max} in;
    signal output {max} out;
    
    assert(out.max <= n);
    
    out.max = n;
    out <== in;
}

template ConstantToBinary(ct){
    signal output {binary} out;
    
    assert(0 <= ct && ct <= 1);
    out <== ct;
}

template ConstantToMaxbit(ct, n){
    signal output {maxbit} out;
    
    assert(0 <= ct && ct < 2**n);
    out.maxbit = n;
    out <== ct;
}

template ConstantToMaxvalue(ct, n){
    signal output {max} out;
    
    assert(0 <= ct && ct < n);
    out.max = n;
    out <== ct;
}
