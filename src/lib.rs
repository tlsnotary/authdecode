use ark_ff::FftField;
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;

mod r_binary;
mod r_decode;
pub mod subslice_revelation;

// Label for referring to the plaintext polynomial in the AUTHDECODE protocol
pub(crate) const PT_LABEL: &str = "PT";

pub struct Plaintext<F: FftField> {
    pub polyn: DensePolynomial<F>,
    pub bytes: Vec<u8>,
}

pub struct PtCom<F, PC>
where
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
{
    com: PC::Commitment,
    r: PC::Randomness,
}
