use std::num::Wrapping; // allows us to do arithmetic on a mod basis
use std::iter::{repeat_n};
use std::array;

const K_RAW: [u32; 64] = [
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 
	0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 
	0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 
	0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 
	0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 
	0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 
	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 
	0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 
	0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 
	0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 
	0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 
	0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 
	0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 
	0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3, 
	0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 
	0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2, 
];

const H: [u32; 8] = [
	0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
	0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

// bit of a hack because I want to keep K as a const, but I also want to use Wrapping.
// with const fns (and current versions of Rust) can't use .map or for loops so will use this solution:
const fn wrap(xs: [u32; 64]) -> [Wrapping<u32>; 64] {
    let mut out = [Wrapping(0u32); 64];
    let mut i = 0;
    while i < 64 {
        out[i] = Wrapping(xs[i]);
        i += 1;
    }
    out
}
const K: [Wrapping<u32>; 64] = wrap(K_RAW);

fn ch(x: Wrapping<u32>, y: Wrapping<u32>, z: Wrapping<u32>) -> Wrapping<u32> {
    (x & y) ^ (!x & z)
}

fn maj(x: Wrapping<u32>, y: Wrapping<u32>, z: Wrapping<u32>) -> Wrapping<u32> {
    (x & y) ^ (x & z) ^ (y & z)
}

// Not using wrapping's rotate_right for the moment.
fn bsigma0(x: Wrapping<u32>) -> Wrapping<u32> {
    Wrapping(x.0.rotate_right(2) ^ x.0.rotate_right(13) ^ x.0.rotate_right(22))
}

fn bsigma1(x: Wrapping<u32>) -> Wrapping<u32> {
    Wrapping(x.0.rotate_right(6) ^ x.0.rotate_right(11) ^ x.0.rotate_right(25))
}

fn ssigma0(x: Wrapping<u32>) -> Wrapping<u32> {
    Wrapping(x.0.rotate_right(7) ^ x.0.rotate_right(18) ^ (x.0 >> 3))
}

fn ssigma1(x: Wrapping<u32>) -> Wrapping<u32> {
    Wrapping(x.0.rotate_right(17) ^ x.0.rotate_right(19) ^ (x.0 >> 10))
}

#[derive(Clone)]
struct Sha256 {
    hash: [Wrapping<u32>; 8],
    buffer: Vec<u8>,
    total_len: u64,
}

#[allow(dead_code)] // switch off unused functions and structs
impl Sha256 {
    pub fn new() -> Self {
        Sha256 {
            hash: H.map(Wrapping),
            buffer: Vec::new(),
            total_len: 0,
        }
    }

    fn block_decomposer(&self, block: &[u8; 64]) -> [Wrapping<u32>; 64] {
        let mut words = [Wrapping(0u32); 64];
        
        // Parse the 512-bit block into the first 16 32-bit words
        block.chunks_exact(4)
            .enumerate()
            .for_each(|(i, chunk)| {
                // unwrap() ok because chunk_exact ensures chunk length can only be 4.
                let bytes: [u8; 4] = chunk.try_into().unwrap();
                words[i] = Wrapping(u32::from_be_bytes(bytes));
            });

        // Extend using the message schedule
        for i in 16..64 {
            words[i] = words[i - 16] + ssigma0(words[i - 15]) 
                    + words[i - 7] + ssigma1(words[i - 2]);
        }

        words
    }

    fn hash_block(&mut self, block: &[u8; 64]) {
        let words = self.block_decomposer(block);

        let [mut a, 
            mut b, 
            mut c, 
            mut d, 
            mut e, 
            mut f, 
            mut g, 
            mut h] = self.hash;

        for (i, word) in words.iter().enumerate() {
            let s1 = bsigma1(e);
            let ch = ch(e, f, g);
            let t1 = h + s1 + ch + K[i] + word;
            let s0 = bsigma0(a);
            let maj = maj(a, b, c);
            let t2 = s0 + maj;

            h = g;
            g = f;
            f = e;
            e = d + t1;
            d = c;
            c = b;
            b = a;
            a = t1 + t2;
        }

        self.hash
            .iter_mut()
            .zip([a, b, c, d, e, f, g, h])
            .for_each(|(h, y)| *h += y);

    }

    pub fn update(&mut self, data: &[u8]) {
        // Combine buffer with new data
        let mut combined = self.buffer.clone();
        combined.extend_from_slice(data);
        
        // Process complete blocks
        let chunks = combined.chunks_exact(64);
        let remainder = chunks.remainder().to_vec();

        for chunk in chunks {
            let block: &[u8; 64] = chunk.try_into().unwrap();
            self.hash_block(block);
        }
        // Store remainder in the buffer and update the message length
        self.buffer = remainder;
        self.total_len += data.len() as u64;
    }

    pub fn finish(&mut self) -> [u8; 32] {
        // Pad the remaining buffer
        let padded = self.pad();
        
        // Process the padded blocks
        for chunk in padded.chunks_exact(64) {
            let block: &[u8; 64] = chunk.try_into().unwrap();
            self.hash_block(block);
        }

        let result: [u8; 32] = array::from_fn(|i| {
            let word_idx = i / 4;
            let byte_idx = i % 4;
            self.hash[word_idx].0.to_be_bytes()[byte_idx]
        });

        result
    }
    
    fn pad(&self) -> Vec<u8> {
        // Total message length in bits.
        let total_bits = self.total_len * 8; // turn number of u32s into bits
        let ln = self.buffer.len();
        let rem = (ln + 1) % 64;
        let k = (64 + 56 - rem) % 64;
            
        let mut out = Vec::with_capacity(ln + 1 + k + 8);
        out.extend_from_slice(&self.buffer);
        out.push(0x80);
        out.extend(repeat_n(0x00, k));
        out.extend_from_slice(&total_bits.to_be_bytes());
        out
    }

}



#[cfg(test)]
mod tests {
    use sha2::{Sha256, Digest};
    use hex_literal::hex;

    fn assert_value(input: &[u8]) {
        let mut hash = super::Sha256::new();
        hash.update(input);
        let act = hash.finish();
        let exp = Sha256::digest(input);
        assert_eq!(act, *exp);
    }

    #[test]
    fn basic() {
        assert_value(b""); 
        assert_value( b"abc");
        assert_value( b"message digest");
        let v = vec![b'a'; 1000000];
        assert_value( &v);
    }

    #[test]
    fn multiple_updates() {
        let mut hash = super::Sha256::new();
        hash.update(b"hello ");
        hash.update(b"world");
        let act = hash.finish();
        assert_eq!(act, hex!("b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"));

    }

    #[test]
    fn test_padding_threshold() {
        assert_value( &[0u8; 56]); // edge of padding
        assert_value( &[0u8; 60]); // check underflow on padding
        assert_value( &[0u8; 63]); // One byte short of full block
    }


}
