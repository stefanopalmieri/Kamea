/// The Ψ₁₆ᶠ Cayley table. 256 bytes. Fits in L1 cache.
/// Copied exactly from psi_star.py's TABLE constant.
pub const TABLE: [[u8; 16]; 16] = [
    [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
    [5,1,13,7,11,5,6,8,2,5,11,9,4,14,3,15],
    [0,1,0,0,0,0,1,1,1,0,1,1,0,0,1,1],
    [0,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],
    [0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,0],
    [15,0,5,9,3,15,14,14,2,12,8,14,12,4,12,8],
    [0,1,8,4,13,2,11,2,14,3,15,12,14,15,6,5],
    [12,1,13,7,11,5,12,11,4,12,5,14,15,7,11,12],
    [1,6,14,14,14,14,9,8,3,15,5,7,13,11,12,4],
    [13,1,4,3,12,11,2,11,5,3,8,14,9,7,11,11],
    [14,1,9,10,11,13,12,7,5,6,8,2,14,12,10,4],
    [0,1,1,0,1,1,0,1,1,1,0,0,0,0,0,1],
    [3,0,14,4,14,6,11,12,7,3,15,10,14,2,6,8],
    [14,0,5,4,3,2,12,5,11,14,3,14,12,2,6,3],
    [1,3,13,15,3,7,14,8,15,4,11,6,7,14,12,10],
];

/// Element names for debugging.
pub const NAMES: [&str; 16] = [
    "⊤", "⊥", "f", "τ", "g", "5", "Q", "E",
    "ρ", "η", "Y", "11", "12", "13", "14", "15",
];

/// Role constants — axiom-forced elements.
pub const TOP: u8 = 0;
pub const BOT: u8 = 1;
pub const F_ENC: u8 = 2;
pub const TAU: u8 = 3;
pub const G_ENC: u8 = 4;
pub const Q: u8 = 6;
pub const E: u8 = 7;
pub const RHO: u8 = 8;
pub const ETA: u8 = 9;
pub const Y_COMB: u8 = 10;

/// One dot operation — the entire algebra.
#[inline(always)]
pub fn dot(a: u8, b: u8) -> u8 {
    TABLE[a as usize][b as usize]
}
