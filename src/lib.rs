use core::ops::RangeInclusive;
use std::collections::BTreeMap;

use ark_ff::FftField;
use ark_poly::{
    polynomial::univariate::DensePolynomial, EvaluationDomain, Evaluations, Polynomial,
};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment, QuerySet};
use rand_core::{CryptoRng, RngCore};

const PT_LABEL: &str = "PT";
const QUOTIENT_LABEL: &str = "q";
const BINARY_CHAL_LABEL: &str = "binchal";

pub struct Plaintext<F: FftField> {
    polyn: DensePolynomial<F>,
    bytes: Vec<u8>,
}

pub struct PtCom<F, PC>
where
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
{
    com: PC::Commitment,
    r: PC::Randomness,
}

impl<F: FftField> Plaintext<F> {
    pub fn commit<PC, R>(&self, mut rng: R, ck: &PC::CommitterKey) -> PtCom<F, PC>
    where
        PC: PolynomialCommitment<F, DensePolynomial<F>>,
        R: RngCore + CryptoRng,
    {
        let labeled_polyn =
            LabeledPolynomial::new(PT_LABEL.to_string(), self.polyn.clone(), None, None);
        let (coms, rands) = PC::commit(ck, &[labeled_polyn], Some(&mut rng)).unwrap();
        PtCom {
            com: coms[0].commitment().clone(),
            r: rands[0].clone(),
        }
    }
}

pub fn prove_binary<D, F, PC, R>(
    mut rng: R,
    domain: D,
    ck: &PC::CommitterKey,
    chal: F,
    pt: &Plaintext<F>,
    pt_com: &PtCom<F, PC>,
) -> PC::BatchProof
where
    D: EvaluationDomain<F>,
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    R: RngCore + CryptoRng,
{
    // Make the polynomial 1ⁿ = (1,1, ..., 1)
    let ones = vec![F::one(); pt.polyn.coeffs.len()];
    let ones_polyn = Evaluations::from_vec_and_domain(ones, domain).interpolate();

    // Construct p-1ⁿ
    let pt_minus_ones = &pt.polyn - &ones_polyn;

    // Multiply: z = p·(p-1ⁿ)
    let z = &pt.polyn * &pt_minus_ones;
    // Compute and commit to q = z / v where v is the polyn that vanishes on the support of `p`
    let (q, _r) = z.divide_by_vanishing_poly(domain).unwrap();

    // Commit to q
    let labeled_q = LabeledPolynomial::new(QUOTIENT_LABEL.to_string(), q.clone(), None, None);
    let (q_coms, q_rands) = PC::commit(ck, &[labeled_q.clone()], Some(&mut rng)).unwrap();
    let q_com = q_coms[0].clone();
    let q_rand = q_rands[0].clone();

    // TODO: Make this a a real challenge point
    let c = F::rand(&mut rng);

    let pt_labeled_polyn =
        LabeledPolynomial::new(PT_LABEL.to_string(), pt.polyn.clone(), None, None);
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

    PC::batch_open(
        &ck,
        &[pt_labeled_polyn, labeled_q],
        &[pt_labeled_com, q_com],
        &query_set,
        chal,
        rands,
        None,
    )
    .unwrap()
}

pub fn prove_subslice<D, F, PC>(
    dom: D,
    ck: &PC::CommitterKey,
    chal: F,
    pt: &Plaintext<F>,
    pt_com: &PtCom<F, PC>,
    slice_idxs: RangeInclusive<usize>,
) -> PC::BatchProof
where
    D: EvaluationDomain<F>,
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
{
    let labeled_polyn = LabeledPolynomial::new(PT_LABEL.to_string(), pt.polyn.clone(), None, None);
    let labeled_com = LabeledCommitment::new(PT_LABEL.to_string(), pt_com.com.clone(), None);

    // A map of "p" -> ("i", ωⁱ). This tells the prover that query i is the i-th byte in the
    // plaintext
    let query_set: QuerySet<F> = slice_idxs
        .clone()
        .map(|i| (PT_LABEL.to_string(), (format!("{i}"), dom.element(i))))
        .collect();

    // The randomness associated with the pt commitment
    let rand = pt_com.r.clone();

    PC::batch_open(
        &ck,
        &[labeled_polyn],
        &[labeled_com],
        &query_set,
        chal,
        &[rand],
        None,
    )
    .unwrap()
}

pub fn check_subslice_proof<D, F, PC, R>(
    mut rng: R,
    dom: D,
    vk: &PC::VerifierKey,
    proof: &PC::BatchProof,
    chal: F,
    pt_com: &PtCom<F, PC>,
    subslice_vals: Vec<F>,
    slice_idxs: RangeInclusive<usize>,
) -> bool
where
    D: EvaluationDomain<F>,
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    R: CryptoRng + RngCore,
{
    let labeled_com = LabeledCommitment::new(PT_LABEL.to_string(), pt_com.com.clone(), None);

    // A map of "p" -> ("i", ωⁱ). This tells the verifier that query i is the i-th byte in the
    // plaintext
    let query_set: QuerySet<F> = slice_idxs
        .clone()
        .map(|i| (PT_LABEL.to_string(), (format!("{i}"), dom.element(i))))
        .collect();

    // A map of (label, "i") -> pt[i]. This tells the verifier the value of the i-th plaintext byte
    let evals: BTreeMap<(String, F), F> = slice_idxs
        .clone()
        .map(|i| (PT_LABEL.to_string(), dom.element(i)))
        .zip(subslice_vals.into_iter())
        .collect();

    PC::batch_check(
        &vk,
        &[labeled_com],
        &query_set,
        &evals,
        &proof,
        chal,
        &mut rng,
    )
    .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use ark_poly::{EvaluationDomain, Evaluations, Radix2EvaluationDomain as D};
    use ark_std::test_rng;
    use rand::Rng;

    use ark_bls12_381::{Bls12_381 as E, Fr as F};
    use ark_ec::PairingEngine;
    use ark_poly_commit::{
        ipa_pc::InnerProductArgPC, marlin::marlin_pc::MarlinKZG10, sonic_pc::SonicKZG10,
    };
    //use ark_vesta::{Affine as G, Fr as F};
    //type PC = SonicKZG10<E, DensePolynomial<F>>;
    type PC = MarlinKZG10<E, DensePolynomial<F>>;
    //type PC = InnerProductArgPC<G, blake2::Blake2s, DensePolynomial<F>>;

    #[test]
    fn test_prove_binary() {
        let pt_bytelen = 1 << 15;

        // Set up the RNG, the polynomial evaluation domain, and the SRS for commitments
        let mut rng = test_rng();
        let domain = D::new(pt_bytelen).unwrap();
        let universal_params = PC::setup(pt_bytelen * 4, None, &mut rng).unwrap();
        let (ck, vk) = PC::trim(&universal_params, pt_bytelen, 2, None).unwrap();

        // Make a random plaintext and commit to it
        let pt_bytes: Vec<u8> = core::iter::repeat_with(|| rng.gen::<u8>())
            .take(pt_bytelen)
            .collect();
        let pt_polyn = Evaluations::from_vec_and_domain(
            pt_bytes.clone().into_iter().map(F::from).collect(),
            domain,
        )
        .interpolate();
        let pt = Plaintext {
            polyn: pt_polyn,
            bytes: pt_bytes,
        };
        let pt_com: PtCom<F, PC> = pt.commit(&mut rng, &ck);

        let chal = F::rand(&mut rng);

        prove_binary(&mut rng, domain, &ck, chal, &pt, &pt_com);

        // TODO: Check binary proof
    }

    #[test]
    fn test_open_subslice() {
        for log_pt_bytelen in 10..16 {
            let pt_bytelen = 1 << log_pt_bytelen;

            // Set up the RNG, the polynomial evaluation domain, and the SRS for commitments
            let mut rng = test_rng();
            let domain = D::new(pt_bytelen).unwrap();
            let universal_params = PC::setup(pt_bytelen * 4, None, &mut rng).unwrap();
            let (ck, vk) = PC::trim(&universal_params, pt_bytelen, 2, None).unwrap();

            // Make a random plaintext and commit to it
            let pt_bytes: Vec<u8> = core::iter::repeat_with(|| rng.gen::<u8>())
                .take(pt_bytelen)
                .collect();
            let pt_vals: Vec<F> = pt_bytes.iter().cloned().map(F::from).collect();
            let pt_polyn = Evaluations::from_vec_and_domain(
                pt_bytes.clone().into_iter().map(F::from).collect(),
                domain,
            )
            .interpolate();

            // Sanity check: make sure pt_vals is actually pt_polyn(i) for all i
            pt_vals
                .iter()
                .enumerate()
                .for_each(|(i, v)| assert_eq!(*v, pt_polyn.evaluate(&domain.element(i))));

            let pt = Plaintext {
                polyn: pt_polyn,
                bytes: pt_bytes,
            };
            let pt_com: PtCom<F, PC> = pt.commit(&mut rng, &ck);

            for slice_size in 1..16 {
                let chal = F::rand(&mut rng);
                let slice = 0..=(slice_size - 1);

                let start = std::time::Instant::now();
                let proof = prove_subslice(domain, &ck, chal, &pt, &pt_com, slice.clone());
                let proof_time = start.elapsed().as_millis();

                let start = std::time::Instant::now();
                let verif = check_subslice_proof(
                    &mut rng,
                    domain,
                    &vk,
                    &proof,
                    chal,
                    &pt_com,
                    pt_vals.clone(),
                    slice.clone(),
                );
                let verif_time = start.elapsed().as_millis();
                assert!(verif);

                println!(
                    "Opening {slice_size}/2^{log_pt_bytelen} elems: \
                    {proof_time}ms / {verif_time}ms (proof/verif)",
                );
            }
        }
    }
}
