pragma circom 2.0.0;

include "../../circuits/mux1.circom";
include "../../circuits/bitify.circom";


template Constants() {
    var i;
    signal output out[2];

    out[0] <== 37;
    out[1] <== 47;
    
    spec_postcondition out[0] == 37;
    spec_postcondition out[1] == 47;
}

template Main() {
    var i;
    signal input selector;//private
    signal output out;

    component mux = Mux1();
    component n2b = Num2Bits(1);
    component cst = Constants();

    selector ==> n2b.in;
    n2b.out[0] ==> mux.s;
    for (i=0; i<2; i++) {
        cst.out[i] ==> mux.c[i];
    }

    mux.out ==> out;
    
    spec_postcondition (selector == 0) => (out == 37); 
    spec_postcondition (selector == 1) => (out == 47); 
    spec_postcondition (0 <= selector) && (selector <= 1);
}

component main = Main();
