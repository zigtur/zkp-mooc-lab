pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    assert(b < 254);
    signal input in;
    signal output out;
    signal inBits[b];
    signal inv;
    var bitsum = 0;
    var calc=0;

    // TODO
    for (var i = 0; i < b; i++) {
        inBits[i] <-- (in >> i) & 1;
        inBits[i] * (1 - inBits[i]) === 0;
    }

    component B2n = Bits2Num(b);
    B2n.bits <== inBits;
    signal inTested <== B2n.out;

    component isZero = IsZero();
    isZero.in <== in - inTested;

    out <== isZero.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    assert(shift < b);
    signal input x;
    signal output y;

    component x_length_validity = CheckBitLength(b);
    x_length_validity.in <== x;
    1 === x_length_validity.out;

    signal shiftedX <-- x >> shift;

    // if x is shifted by 'shift' bits
    // then the shifted bits that disappears must be less than 2^(shift+1)

    signal shiftedBits <-- x - (shiftedX << shift);
    component lessThan = LessThan(shift+1);
    lessThan.in[0] <== shiftedBits;
    lessThan.in[1] <== (1 << (shift+1));
    lessThan.out === 1;

    y <== shiftedX;
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(P+1, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    component isEqual[shift_bound];
    var multiplication = 0;

    for (var i = 0; i < shift_bound; i++) {
        isEqual[i] = IsEqual();

        isEqual[i].in[0] <== i;
        isEqual[i].in[1] <== shift;
        multiplication += isEqual[i].out * (1<<i);
    }

    // calculating y
    y <== multiplication * x;

    var shift_bound_bit = 0;
    while ((1<<shift_bound_bit) <= shift_bound) {
        shift_bound_bit++;
    }

    component Compare = LessThan(shift_bound_bit);
    shift ==> Compare.in[0];
    shift_bound ==> Compare.in[1];   

    component checker = IfThenElse();
    checker.cond <== skip_checks;
    checker.L <== 1;
    checker.R <== Compare.out;

    checker.out === 1;

    // can be improved
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    // TODO
    signal inBits[b];
    component n2b = Num2Bits(b);
    n2b.in <== in;
    inBits <== n2b.bits;



    // inspired from zhuhl98
    signal prod[b];
    prod[b-1] <== 1;
    for (var i = b-2; i >= 0; i--) {
        prod[i] <== prod[i+1] * (1 - inBits[i+1]);
    }

    for (var i = 0; i < b; i++)
        one_hot[i] <== inBits[i] * prod[i];

    
    component checker = IfThenElse();
    checker.cond <== skip_checks;
    checker.L <== 0;
    checker.R <== prod[0]*(1-inBits[0]);

    checker.out === 0;
    



    /*//component lessThanCompare = LessThan(b);
    var save_i = 0;
    var tmp;
    var vinBits = in;

    // Possible to rightshift i times, then compare with 1 --> 
    for (var i = b-1; i >= 0; i--) {
        tmp = 1 << i;
        if (save_i == 0 && tmp & vinBits) {
            save_i = i;
        }
    }

    signal msnzb <-- 1 << save_i;
    component lessThanCompare = LessThan(b);
    lessThanCompare.in[0] <== msnzb;
    lessThanCompare.in[1] <== (in / 2);
    0 === lessThanCompare.out;

    one_hot[save_i] <-- 1 << save_i;*/




}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    component msnzb = MSNZB(P+1);
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;
    
    var e_delta = 0;
    var m_factor = 0;

    for (var i = 0; i <= P; i++) {
        e_delta += msnzb.one_hot[i]*i;
        m_factor += msnzb.one_hot[i]*(1<<(P-i));
    }

    e_out <== e + e_delta - p;
    m_out <== m_factor * m;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    /*
     * check well-formedness
     */
    component checker[2];

    for (var i = 0; i < 2; i++) {
        checker[i] = CheckWellFormedness(k, p);
        checker[i].e <== e[i];
        checker[i].m <== m[i];
    }

    /*
     * comparing e[1] || m[1] against e[2] || m[2] suffices to compare magnitudes.
     */

    component Compare = LessThan(k+p+1);
    for (var i = 0; i < 2; i++) {
        Compare.in[i] <== m[i] + e[i] * (1<<(p+1));
    }

    component eSwitcher = Switcher(); 
    component mSwitcher = Switcher();
    
    eSwitcher.sel <== Compare.out;
    eSwitcher.L <== e[0];
    eSwitcher.R <== e[1];

    mSwitcher.sel <== Compare.out;
    mSwitcher.L <== m[0];
    mSwitcher.R <== m[1];

    var alpha_m = mSwitcher.outL;
    var alpha_e = eSwitcher.outL;
    var beta_m = mSwitcher.outR;
    var beta_e = eSwitcher.outR;

    /*
     *  Check whether diff > p+1 or alpha_e == 0
     */
    signal diff <== alpha_e - beta_e;

    component diff_check = LessThan(k);
    diff_check.in[0] <== p+1;
    diff_check.in[1] <== diff;

    component alpha_e_check = IsZero();
    alpha_e_check.in <== alpha_e;

    component or_check = OR();
    or_check.a <== diff_check.out;
    or_check.b <== alpha_e_check.out;
    
    component if_else_alpha_m = IfThenElse();
    if_else_alpha_m.cond <== or_check.out;
    if_else_alpha_m.L <== 1;
    if_else_alpha_m.R <== alpha_m;

    component if_else_diff = IfThenElse();
    if_else_diff.cond <== or_check.out;
    if_else_diff.L <== 0;
    if_else_diff.R <== diff;

    component if_else_beta_e = IfThenElse();
    if_else_beta_e.cond <== or_check.out;
    if_else_beta_e.L <== 1;
    if_else_beta_e.R <== beta_e;
    /*
     *  adding two floating-point numbers
     */

    component m_alpha_left_shift = LeftShift(p+2);
    m_alpha_left_shift.x <== if_else_alpha_m.out;
    m_alpha_left_shift.shift <== if_else_diff.out;
    m_alpha_left_shift.skip_checks <== 0;

    component normalize = Normalize(k, p, 2*p+1);
    normalize.e <== if_else_beta_e.out;
    normalize.m <== m_alpha_left_shift.y + beta_m;
    normalize.skip_checks <== 0;

    component round = RoundAndCheck(k, p, 2*p+1);
    round.e <== normalize.e_out;
    round.m <== normalize.m_out;


    component if_else_m = IfThenElse();
    if_else_m.cond <== or_check.out;
    if_else_m.L <== alpha_m;
    if_else_m.R <== round.m_out;

    component if_else_e = IfThenElse();
    if_else_e.cond <== or_check.out;
    if_else_e.L <== alpha_e;
    if_else_e.R <== round.e_out;

    e_out <== if_else_e.out;
    m_out <== if_else_m.out;

}