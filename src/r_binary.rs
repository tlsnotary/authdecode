use crate::{PtCom, PT_LABEL};

use std::collections::BTreeMap;

use ark_ff::FftField;
use ark_poly::{
    polynomial::univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial,
};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment, QuerySet};
use num_traits::identities::Zero;
use rand_core::{CryptoRng, RngCore};

// Labels for referring to polynomials and scalars in the R_binary protocol
const QUOTIENT_LABEL: &str = "q";
const BINARY_CHAL_LABEL: &str = "binchal";

pub(crate) struct BinarynessProof<F, PC>
where
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
{
    /// The proof of correct evaluation of `pt_chal_eval` and `quotient_chal_eval`
    eval_proof: PC::BatchProof,
    /// The point `q(c)` for some challenge point `c`, where `q` is the "quotient polynomial"
    /// define in the protocol
    quotient_com: LabeledCommitment<PC::Commitment>,
    /// The point `p(c)` for some challenge point `c`
    pt_chal_eval: F,
    /// The point `q(c)` for some challenge point `c`
    quotient_chal_eval: F,
}

/// Proves that the given plaintext `pt_polyn` has only binary coefficients. `chal` is the
/// challenge point given by the verifier.
pub(crate) fn prove_binary<D, F, PC, R>(
    mut rng: R,
    domain: D,
    ck: &PC::CommitterKey,
    chal: F,
    pt_polyn: &DensePolynomial<F>,
    pt_com: &PtCom<F, PC>,
) -> BinarynessProof<F, PC>
where
    D: EvaluationDomain<F>,
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    R: RngCore + CryptoRng,
{
    // Make the polynomial 1ⁿ = (1,1, ..., 1)
    let ones = vec![F::one(); pt_polyn.coeffs.len()];
    let ones_polyn = Evaluations::from_vec_and_domain(ones, domain).interpolate();

    // Construct p-1ⁿ
    let pt_minus_ones = pt_polyn - &ones_polyn;

    // Multiply: z = p·(p-1ⁿ)
    let z = pt_polyn * &pt_minus_ones;
    // Compute and commit to q = z / v where v is the polyn that vanishes on the support of `p`
    let (q, _r) = z.divide_by_vanishing_poly(domain).unwrap();
    // Sanity check: make sure z is divisible by the vanishing polynoimal
    assert!(_r.is_zero());

    // Commit to q
    let labeled_q = LabeledPolynomial::new(QUOTIENT_LABEL.to_string(), q.clone(), None, None);
    let (q_coms, q_rands) = PC::commit(ck, &[labeled_q.clone()], Some(&mut rng)).unwrap();
    let q_com = q_coms[0].clone();
    let q_rand = q_rands[0].clone();

    // TODO: Make this a a real challenge point
    let c = F::from(1337u16);

    let pc = pt_polyn.evaluate(&c);
    let qc = q.evaluate(&c);

    // Sanity check: make sure qc * vc == zc
    assert_eq!(qc * domain.evaluate_vanishing_polynomial(c), z.evaluate(&c));

    let pt_labeled_polyn =
        LabeledPolynomial::new(PT_LABEL.to_string(), pt_polyn.clone(), None, None);
    let pt_labeled_com = LabeledCommitment::new(PT_LABEL.to_string(), pt_com.com.clone(), None);

    // A map telling the prover to prove the values of p(c) and q(c)
    let query_set: QuerySet<F> = [
        (PT_LABEL.to_string(), (BINARY_CHAL_LABEL.to_string(), c)),
        (
            QUOTIENT_LABEL.to_string(),
            (BINARY_CHAL_LABEL.to_string(), c),
        ),
    ]
    .into_iter()
    .collect();

    // The openings to the commitments to p and q
    let rands = &[pt_com.r.clone(), q_rand];

    let batch_proof = PC::batch_open(
        &ck,
        &[pt_labeled_polyn, labeled_q],
        &[pt_labeled_com, q_com.clone()],
        &query_set,
        chal,
        rands,
        None,
    )
    .unwrap();

    BinarynessProof {
        eval_proof: batch_proof,
        quotient_com: q_com,
        pt_chal_eval: pc,
        quotient_chal_eval: qc,
    }
}

/// Verifies that the plaintext committed to by `pt_com` has only binary coefficients. `chal` is
/// the challenge point given by the verifier. `q`, `pc`, and `qc` are all given by the prover.
pub(crate) fn verif_binary<D, F, PC, R>(
    mut rng: R,
    domain: D,
    deg: usize,
    vk: &PC::VerifierKey,
    chal: F,
    pt_com: &PtCom<F, PC>,
    proof: &BinarynessProof<F, PC>,
) -> bool
where
    D: EvaluationDomain<F>,
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    R: RngCore + CryptoRng,
{
    // Destructure the proof
    let BinarynessProof {
        eval_proof,
        quotient_com,
        pt_chal_eval,
        quotient_chal_eval,
    } = proof;

    // TODO: Make this a a real challenge point
    let c = F::from(1337u16);

    // Wrap the commitment
    let pt_labeled_com = LabeledCommitment::new(PT_LABEL.to_string(), pt_com.com.clone(), None);

    // A map telling the verifier to verifier the values of p(c) and q(c)
    let query_set: QuerySet<F> = [
        (PT_LABEL.to_string(), (BINARY_CHAL_LABEL.to_string(), c)),
        (
            QUOTIENT_LABEL.to_string(),
            (BINARY_CHAL_LABEL.to_string(), c),
        ),
    ]
    .into_iter()
    .collect();

    // A map from the challenge point c to the evaluated points p(c) and q(c)
    let evals: BTreeMap<(String, F), F> = [
        ((PT_LABEL.to_string(), c), *pt_chal_eval),
        ((QUOTIENT_LABEL.to_string(), c), *quotient_chal_eval),
    ]
    .into_iter()
    .collect();

    // Check that pc and qc are the correct evaluations
    let mut res = PC::batch_check(
        &vk,
        &[pt_labeled_com, quotient_com.clone()],
        &query_set,
        &evals,
        eval_proof,
        chal,
        &mut rng,
    )
    .unwrap();

    // Make the polynomial 1ⁿ = (1,1, ..., 1)
    let ones = vec![F::one(); deg];
    let ones_polyn = Evaluations::from_vec_and_domain(ones, domain).interpolate();
    let oc = ones_polyn.evaluate(&c);

    let vc = domain.evaluate_vanishing_polynomial(c);

    // Check that vc · qc == pc · (pc - 1c). This proves that p is binary
    res &= vc * quotient_chal_eval == *pt_chal_eval * (*pt_chal_eval - oc);

    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use ark_poly::{EvaluationDomain, Evaluations, Radix2EvaluationDomain as D};
    use ark_std::test_rng;
    use rand::Rng;

    use ark_bls12_381::{Bls12_381 as E, Fr as F};
    use ark_poly_commit::marlin::marlin_pc::MarlinKZG10;

    // Some alternate polynomial commitment schemes
    //use ark_vesta::{Affine as G, Fr as F};
    //type PC = SonicKZG10<E, DensePolynomial<F>>;
    type PC = MarlinKZG10<E, DensePolynomial<F>>;
    //type PC = InnerProductArgPC<G, blake2::Blake2s, DensePolynomial<F>>;

    // Tests the R_binary relation
    #[test]
    fn test_prove_binary() {
        let log_pt_bitlen = 15;
        let pt_bitlen = 1 << log_pt_bitlen;

        // Set up the RNG, the polynomial evaluation domain, and the SRS for commitments
        let mut rng = test_rng();
        let domain = D::new(pt_bitlen).unwrap();
        let universal_params = PC::setup(pt_bitlen * 4, None, &mut rng).unwrap();
        let (ck, vk) = PC::trim(&universal_params, pt_bitlen, 2, None).unwrap();

        // Make a random plaintext and turn it into a polynomial
        let pt_bits: Vec<bool> = core::iter::repeat_with(|| rng.gen::<bool>())
            .take(pt_bitlen)
            .collect();
        let pt_polyn = Evaluations::from_vec_and_domain(
            pt_bits.clone().into_iter().map(F::from).collect(),
            domain,
        )
        .interpolate();

        // Commit to the polynomial
        let pt_com = {
            let labeled_polyn =
                LabeledPolynomial::new(PT_LABEL.to_string(), pt_polyn.clone(), None, None);
            let (coms, rands) = PC::commit(&ck, &[labeled_polyn], Some(&mut rng)).unwrap();
            PtCom {
                com: coms[0].commitment().clone(),
                r: rands[0].clone(),
            }
        };

        // Sample a random challenge point
        let chal = F::rand(&mut rng);

        // Compute an proof of binaryness and time it
        let start = std::time::Instant::now();
        let binaryness_proof =
            prove_binary::<_, _, PC, _>(&mut rng, domain, &ck, chal, &pt_polyn, &pt_com);
        let proof_time = start.elapsed().as_millis();
        println!("Proving R_binary on 2^{log_pt_bitlen} bits: {proof_time}ms");

        // Verify the binaryness proof
        assert!(verif_binary(
            &mut rng,
            domain,
            pt_bitlen,
            &vk,
            chal,
            &pt_com,
            &binaryness_proof,
        ));
    }
}
