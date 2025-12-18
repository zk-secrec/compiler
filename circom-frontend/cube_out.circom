pragma circom 2.0.0;

template Main (num_wit, num_ins) {
    signal input wit[num_wit];
    signal input ins[num_ins];
    signal output out[1];
    var wi = 0;
    var ii = 0;
    signal s1 <== wit[wi];
    wi++;
    signal s2 <== 1 * s1;
    signal s3 <== s2 * s1;
    signal s4 <== s3 * s1;
    out[0] <== s4;
}

component main {public [ins]} = Main(1, 0);
