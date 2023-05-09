pragma circom 2.0.0;

include "../../circuits/smt/smtprocessor.circom";

template SMTProcessor_main(nLevels) {
    signal input oldRoot;
    signal output newRoot;
    signal input siblings[nLevels];
    signal input oldKey;
    signal input oldValue;
    signal input isOld0;
    signal input newKey;
    signal input newValue;
    signal input fnc[2];
    newRoot <== SMTProcessor(nLevels)(oldRoot,siblings,oldKey,oldValue,
                                      AddBinaryTag()(isOld0), newKey,newValue,
                                      AddBinaryArrayTag(2)(fnc));
}

component main = SMTProcessor_main(10);
