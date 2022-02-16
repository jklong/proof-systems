use ark_ff::FftField;

/// Field element helpers
pub trait FieldHelpers<F: FftField> {
    /// Deserialize from bytes
    fn from_bytes(bytes: &[u8]) -> Result<F, &str>;

    /// Deserialize from hex
    fn from_hex(hex: &str) -> Result<F, &str>;

    /// Deserialize from bits
    fn from_bits(bits: &[bool]) -> Result<F, &'static str>;

    /// Serialize to bytes
    fn to_bytes(self) -> Vec<u8>;

    /// Serialize to hex
    fn to_hex(self) -> String;

    /// Serialize to bits
    fn to_bits(self) -> Vec<bool>;
}

impl<F: FftField> FieldHelpers<F> for F {
    fn from_bytes(bytes: &[u8]) -> Result<F, &str> {
        F::deserialize(&mut &*bytes).map_err(|_| "Failed to deserialize field bytes")
    }

    fn from_hex(hex: &str) -> Result<F, &str> {
        let bytes: Vec<u8> = hex::decode(hex).map_err(|_| "Failed to decode field hex")?;
        F::deserialize(&mut &bytes[..]).map_err(|_| "Failed to deserialize field bytes")
    }

    fn from_bits(bits: &[bool]) -> Result<F, &'static str> {
        let bytes = bits
            .iter()
            .enumerate()
            .fold(F::zero().to_bytes(), |mut bytes, (i, bit)| {
                bytes[i / 8] |= (*bit as u8) << (i % 8);
                bytes
            });

        F::deserialize(&mut &bytes[..]).map_err(|_| "Failed to deserialize field bytes")
    }

    fn to_bytes(self) -> Vec<u8> {
        let mut bytes: Vec<u8> = vec![];
        self.serialize(&mut bytes)
            .expect("Failed to serialize field");

        bytes
    }

    fn to_hex(self) -> String {
        hex::encode(self.to_bytes())
    }

    fn to_bits(self) -> Vec<bool> {
        self.to_bytes().iter().fold(vec![], |mut bits, byte| {
            let mut byte = *byte;
            for _ in 0..8 {
                bits.push(byte & 0x01 == 0x01);
                byte >>= 1;
            }
            bits
        })
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::AffineCurve;
    use ark_ff::{One, PrimeField};
    use mina_curves::pasta::pallas;

    // Affine curve point type
    pub use pallas::Affine as CurvePoint;
    // Base field element type
    pub type BaseField = <CurvePoint as AffineCurve>::BaseField;

    use super::*;

    #[test]
    fn field_hex() {
        assert_eq!(
            BaseField::from_hex(""),
            Err("Failed to deserialize field bytes")
        );
        assert_eq!(
            BaseField::from_hex("1428fadcf0c02396e620f14f176fddb5d769b7de2027469d027a80142ef8f07"),
            Err("Failed to decode field hex")
        );
        assert_eq!(
            BaseField::from_hex(
                "0f5314f176fddb5d769b7de2027469d027ad428fadcf0c02396e6280142efb7d8"
            ),
            Err("Failed to decode field hex")
        );
        assert_eq!(
            BaseField::from_hex("g64244176fddb5d769b7de2027469d027ad428fadcf0c02396e6280142efb7d8"),
            Err("Failed to decode field hex")
        );
        assert_eq!(
            BaseField::from_hex("0cdaf334e9632268a5aa959c2781fb32bf45565fe244ae42c849d3fdc7c644fd"),
            Err("Failed to deserialize field bytes")
        );

        assert_eq!(
            BaseField::from_hex("2eaedae42a7461d5952d27b97ecad068b698ebb94e8a0e4c45388bb613de7e08")
                .is_ok(),
            true
        );

        assert_eq!(
            BaseField::to_hex(
                BaseField::from_hex(
                    "2eaedae42a7461d5952d27b97ecad068b698ebb94e8a0e4c45388bb613de7e08"
                )
                .expect("Failed to deserialize field hex")
            ),
            "2eaedae42a7461d5952d27b97ecad068b698ebb94e8a0e4c45388bb613de7e08"
        );
    }

    #[test]
    fn field_bytes() {
        assert_eq!(
            BaseField::from_bytes(&[
                46, 174, 218, 228, 42, 116, 97, 213, 149, 45, 39, 185, 126, 202, 208, 104, 182,
                152, 235, 185, 78, 138, 14, 76, 69, 56, 139, 182, 19, 222, 126, 8
            ])
            .is_ok(),
            true
        );

        assert_eq!(
            BaseField::from_bytes(&[46, 174, 218, 228, 42, 116, 97, 213]),
            Err("Failed to deserialize field bytes")
        );

        assert_eq!(
            BaseField::to_hex(
                BaseField::from_bytes(&[
                    46, 174, 218, 228, 42, 116, 97, 213, 149, 45, 39, 185, 126, 202, 208, 104, 182,
                    152, 235, 185, 78, 138, 14, 76, 69, 56, 139, 182, 19, 222, 126, 8
                ])
                .expect("Failed to deserialize field bytes")
            ),
            "2eaedae42a7461d5952d27b97ecad068b698ebb94e8a0e4c45388bb613de7e08"
        );
    }

    #[test]
    fn field_bits() {
        let fe =
            BaseField::from_hex("2cc3342ad3cd516175b8f0d0189bc3bdcb7947a4cc96c7cfc8d5df10cc443832")
                .expect("Failed to deserialize field hex");

        let fe_check =
            BaseField::from_bits(&fe.to_bits()).expect("Failed to deserialize field bits");
        assert_eq!(fe, fe_check);

        assert_eq!(
            BaseField::from_bits(&[
                false, true, false, false, false, true, true, false, true, true, false, false,
                false, false, true, true, false, false, true, false, true, true, false, false,
                false, true, false, true, false, true, false, false, true, true, false, false,
                true, false, true, true, true, false, true, true, false, false, true, true, true,
                false, false, false, true, false, true, false, true, false, false, false, false,
                true, true, false, true, false, true, false, true, true, true, false, false, false,
                false, true, true, true, false, true, false, false, false, false, true, true, true,
                true, false, false, false, false, true, false, true, true, false, false, false,
                false, true, false, true, false, true, true, false, true, true, false, false, true,
                true, true, false, false, false, false, true, true, true, false, true, true, true,
                true, false, true, true, true, false, true, false, true, true, true, true, false,
                false, true, true, true, true, false, true, true, true, false, false, false, true,
                true, false, false, true, false, false, true, false, true, false, false, true,
                true, false, false, true, true, false, true, true, false, true, false, false, true,
                true, true, true, false, false, false, true, true, true, true, true, true, false,
                false, true, true, false, false, false, true, false, false, true, true, true,
                false, true, false, true, false, true, true, true, true, true, true, true, false,
                true, true, false, false, false, false, true, false, false, false, false, false,
                false, true, false, false, true, true, false, false, true, false, false, false,
                true, false, false, false, false, true, true, true, false, false, false, true,
                true, true, true, false, false
            ])
            .is_ok(),
            true
        );

        assert_eq!(
            BaseField::from_bits(&vec![true; BaseField::size_in_bits()]),
            Err("Failed to deserialize field bytes")
        );

        assert_eq!(
            BaseField::from_bits(&[false, true, false, true]).is_ok(),
            true
        );

        assert_eq!(
            BaseField::from_bits(&[true, false, false]).expect("Failed to deserialize field bytes"),
            BaseField::one()
        );
    }
}
