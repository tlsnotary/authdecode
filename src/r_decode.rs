use crate::{
    r_binary::{prove_binary, BinarynessProof},
    PtCom,
};

use ark_ff::FftField;
use ark_poly::{polynomial::univariate::DensePolynomial, EvaluationDomain, Polynomial};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment};
use rand_core::{CryptoRng, RngCore};

// String to identify the zero-labels polynomial
const ZEROLABELS_LABEL: &str = "W₀";

pub struct ActiveLabelsCom<F, PC>
where
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
{
    com: PC::Commitment,
    r: PC::Randomness,
}

struct DecodeProof<F, PC>
where
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
{
    /// The point `W₀(c)` for some challenge point `c`, where W₀ is the zero-labels polyn
    zero_labels_eval: F,
    /// The proof that `W₀(c)` was evaluated correctly
    zero_labels_eval_proof: PC::Proof,
    /// We call down to R_binary in R_decode. This is that proof
    binaryness_proof: BinarynessProof<F, PC>,
}

/// Proves the `R_decode` relation. That is, that `p` is binary and `zero_labels[i] =
/// active_labels[i] - Δ·p[i]` for all `i`.
fn prove_decode<D, F, PC, R>(
    mut rng: R,
    domain: D,
    ck: &PC::CommitterKey,
    chal: F,
    pt_polyn: &DensePolynomial<F>,
    pt_com: &PtCom<F, PC>,
    active_labels_polyn: &DensePolynomial<F>,
    active_labels_com: &ActiveLabelsCom<F, PC>,
    zero_labels: &DensePolynomial<F>,
    delta: F,
) -> DecodeProof<F, PC>
where
    D: EvaluationDomain<F>,
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    R: RngCore + CryptoRng,
{
    // Eval the zero labels at a challenge value
    // TODO: pick a real challenge value
    let c = F::from(1337u16);
    let zero_labels_eval = zero_labels.evaluate(&c);

    // TODO: Implement scalar multiplication for commitments. It's already the case that
    //     PC::Commitment: for<'a> core::ops::AddAssign<(F, &'a PC::Commitment)>
    // i.e., you can add commitments, but it doesn't mean you can scalar-multiply them
    // This should be `active_labels_com - Δ·pt_com`
    let (rhs_com, rhs_com_rand): (LabeledCommitment<PC::Commitment>, PC::Randomness) =
        unimplemented!();

    // Give a name to zero_labels
    let zero_labels = LabeledPolynomial::new(
        ZEROLABELS_LABEL.to_string(),
        zero_labels.clone(),
        None,
        None,
    );

    // Prove the eval of W₀(c)
    let zero_labels_eval_proof = PC::open(
        &ck,
        &[zero_labels],
        &[rhs_com],
        &c,
        chal,
        &[rhs_com_rand],
        None,
    )
    .unwrap();

    // Now also prove that `pt` is binary
    let binaryness_proof = prove_binary(&mut rng, domain, ck, chal, pt_polyn, pt_com);

    DecodeProof {
        zero_labels_eval,
        zero_labels_eval_proof,
        binaryness_proof,
    }
}
