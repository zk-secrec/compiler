pragma circom 2.0.0;

// This assumes that circomlib has been copied under the directory circom-frontend
include "circomlib/circuits/sha256/sha256_2.circom";

template Main() {
    signal input wit[2];
    signal input ins[0];
    signal output out[1];

    component sha256_2 = Sha256_2();

    sha256_2.a <== wit[0];
    sha256_2.b <== wit[1];
    out[0] <== sha256_2.out;
}

component main {public [ins]} = Main();
