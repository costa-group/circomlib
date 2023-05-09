pragma circom 2.0.0;

include "../../circuits/sha256/sha256.circom";

template Sha256_main(nBits) {
    signal input in[nBits];
    signal output {binary} out[256];

    out <== Sha256(nBits)(AddBinaryArrayTag(nBits)(in));
}

component main = Sha256_main(512);
