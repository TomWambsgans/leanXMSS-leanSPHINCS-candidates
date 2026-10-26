//! The two-level WOTS forest: the few-time signature under each XMSS leaf.
//!
//! An instance has `COORDS = 8` independent coordinates. A coordinate is a top Merkle tree of
//! height 4 over 16 super-children, hashed up to level 3 only: its two level-3 nodes are not hashed
//! into a root, and the forest key is the sixteen nodes themselves, which the WOTS+C encoding
//! absorbs. A super-child hashes the two level-2 nodes of each of its two sub-trees; a sub-tree is a
//! Merkle tree of height 3 over 8 children, also hashed up to its two top nodes only. A child is a
//! small WOTS key: 6 chains of length 5 under a leaf hash, signed at a codeword of digit sum 5.

use std::sync::OnceLock;

use crate::*;

pub const SUPERS: usize = 1 << TOP_HEIGHT;
pub const CHILDREN: usize = 1 << SUB_HEIGHT;

/// The forest key of an instance: the two level-3 nodes of every coordinate's top tree.
pub type ForestKey = [[Digest; 2]; COORDS];

/// What the digest selects in one coordinate: the super-child, and per sub-tree a child and a
/// codeword index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoordMark {
    pub super_child: usize,
    pub child: [usize; SUBS],
    pub word: [u8; SUBS],
}

/// The opening of one sub-tree: the 6 revealed chain values and the 3 authentication nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubOpening {
    pub values: [Digest; CHILD_CHAINS],
    pub path: [Digest; SUB_HEIGHT],
}

/// The opening of one coordinate: both sub-trees, then the 4 authentication nodes of the top tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CoordOpening {
    pub sub: [SubOpening; SUBS],
    pub top: [Digest; TOP_HEIGHT],
}

/// What a signature carries for the forest: `COORDS * 22` values.
pub type ForestOpening = [CoordOpening; COORDS];

/// Values a coordinate's opening carries: per sub-tree 6 chain values and 3 nodes, plus 4 nodes.
pub const VALUES_PER_COORD: usize = SUBS * (CHILD_CHAINS + SUB_HEIGHT) + TOP_HEIGHT;

/// The 256 entries of the codeword table: the 246 vectors `d` in `{0..4}^6` of digit sum 5, sorted
/// by decreasing `sum d_i^2` then lexicographically, entry `t` being codeword number `t mod 214`.
/// Spread-out codewords are easier to forge once a key has signed twice, so the 32 most spread-out
/// ones are left out and the 42 most concentrated ones appear twice.
pub fn codeword_table() -> &'static [[u8; CHILD_CHAINS]; 256] {
    static TABLE: OnceLock<[[u8; CHILD_CHAINS]; 256]> = OnceLock::new();
    TABLE.get_or_init(|| {
        // base-5 codes in increasing order, i.e. digit vectors in lexicographic order
        let mut words: Vec<[u8; CHILD_CHAINS]> = (0..5usize.pow(CHILD_CHAINS as u32))
            .map(|code| std::array::from_fn(|i| (code / 5usize.pow((CHILD_CHAINS - 1 - i) as u32) % 5) as u8))
            .filter(|d: &[u8; CHILD_CHAINS]| d.iter().map(|&x| x as usize).sum::<usize>() == CODEWORD_SUM)
            .collect();
        words.sort_by_key(|d| std::cmp::Reverse(d.iter().map(|&x| (x as u32) * (x as u32)).sum::<u32>()));
        std::array::from_fn(|t| words[t % 214])
    })
}

/// `lut t`: the codeword of table entry `t`, the deficit of each of the 6 chains.
pub fn lut(t: u8) -> [u8; CHILD_CHAINS] {
    codeword_table()[t as usize]
}

/// `c + 8 s + 128 j`, a sub-tree of the instance.
fn sub_slot(c: usize, s: usize, j: usize) -> u32 {
    assert!(c < COORDS && s < SUPERS && j < SUBS);
    (c + 8 * s + 128 * j) as u32
}

/// `c + 8 s + 128 j + 256 a`, a child of the instance.
fn child_slot(c: usize, s: usize, j: usize, a: usize) -> u32 {
    assert!(a < CHILDREN);
    sub_slot(c, s, j) + 256 * a as u32
}

/// `c + 8 s + 128 j + 256 a + 2048 i`, a chain of the instance.
fn chain_slot(c: usize, s: usize, j: usize, a: usize, i: usize) -> u32 {
    assert!(i < CHILD_CHAINS);
    child_slot(c, s, j, a) + 2048 * i as u32
}

/// The address of the hash that gives the starts of chains `2 t` and `2 t + 1` of a child.
pub fn forest_secret_tweak(idx: u64, c: usize, s: usize, j: usize, a: usize, t: usize) -> Tweak {
    debug_assert!(t < CHILD_CHAINS / 2);
    tweak(TWEAK_FOREST_PRF, child_slot(c, s, j, a) + 2048 * t as u32, idx as u32)
}

/// The starts of the 6 chains of a child: one hash of the seed gives two of them.
pub fn child_secrets(
    pp: &Pp, master: &MasterSecret, idx: u64, c: usize, s: usize, j: usize, a: usize,
) -> [Digest; CHILD_CHAINS] {
    let mut starts = [[0u8; N]; CHILD_CHAINS];
    for t in 0..CHILD_CHAINS / 2 {
        let pair = th_pair(pp, &forest_secret_tweak(idx, c, s, j, a, t), master);
        starts[2 * t] = pair[0];
        starts[2 * t + 1] = pair[1];
    }
    starts
}

/// The tweak of the forest chain step that leaves position `from < 4`.
fn fchain_tweak(idx: u64, c: usize, s: usize, j: usize, a: usize, i: usize, from: usize) -> Tweak {
    debug_assert!(from < CHAIN_TOP);
    tweak(TWEAK_FCHAIN, chain_slot(c, s, j, a, i), idx as u32).step(from)
}

/// `steps` chain steps from position `start`.
#[allow(clippy::too_many_arguments)]
pub fn forest_chain(
    pp: &Pp, idx: u64, c: usize, s: usize, j: usize, a: usize, i: usize,
    start: usize, steps: usize, value: Digest,
) -> Digest {
    debug_assert!(start + steps <= CHAIN_TOP);
    (start..start + steps).fold(value, |current, from| th(pp, &fchain_tweak(idx, c, s, j, a, i, from), &current))
}

/// The leaf of a child: the hash of its 6 chain tops.
pub fn child_leaf(
    pp: &Pp, idx: u64, c: usize, s: usize, j: usize, a: usize, tops: &[Digest; CHILD_CHAINS],
) -> Digest {
    th_digests(pp, &tweak(TWEAK_CHILD_LEAF, child_slot(c, s, j, a), idx as u32), tops)
}

/// A node of a sub-tree: `level` counts from the leaves, so this is the node of level `level + 1`.
fn sub_node(
    pp: &Pp, idx: u64, c: usize, s: usize, j: usize, level: usize, node: usize,
    left: &Digest, right: &Digest,
) -> Digest {
    let hi = sub_slot(c, s, j) + 256 * (level as u32 + 1) + 1024 * node as u32;
    th_digests(pp, &tweak(TWEAK_SUB_NODE, hi, idx as u32), &[*left, *right])
}

/// A super-child: the hash of the two level-2 nodes of each of its two sub-trees.
fn super_child(pp: &Pp, idx: u64, c: usize, s: usize, tops: &[[Digest; 2]; SUBS]) -> Digest {
    th_digests(
        pp,
        &tweak(TWEAK_SUPER_CHILD, (c + 8 * s) as u32, idx as u32),
        &[tops[0][0], tops[0][1], tops[1][0], tops[1][1]],
    )
}

/// A node of a top tree, of level `level + 1`.
fn top_node(
    pp: &Pp, idx: u64, c: usize, level: usize, node: usize, left: &Digest, right: &Digest,
) -> Digest {
    let hi = (c + 8 * (level + 1) + 64 * node) as u32;
    th_digests(pp, &tweak(TWEAK_TOP_NODE, hi, idx as u32), &[*left, *right])
}

/// The two top nodes in index order, from the one a fold reached and the last path element.
fn order_tops(bit: bool, current: Digest, sibling: Digest) -> [Digest; 2] {
    if bit { [sibling, current] } else { [current, sibling] }
}

/// A forest instance whose children are known: every level, kept for the openings.
pub struct Forest {
    /// `starts[c][s][j][a][i]`: the start of every chain.
    starts: Vec<Digest>,
    /// `sub[c][s][j][level][node]`, level 0 being the 8 child leaves and level 2 the two top nodes.
    sub: Vec<Levels>,
    /// `top[c][level][node]`, level 0 being the 16 super-children and level 3 the two top nodes.
    top: Vec<Levels>,
    key: ForestKey,
}

/// `(((c * SUPERS + s) * SUBS + j) * CHILDREN + a) * CHILD_CHAINS + i`.
fn chain_index(c: usize, s: usize, j: usize, a: usize, i: usize) -> usize {
    (((c * SUPERS + s) * SUBS + j) * CHILDREN + a) * CHILD_CHAINS + i
}

fn sub_index(c: usize, s: usize, j: usize) -> usize {
    (c * SUPERS + s) * SUBS + j
}

impl Forest {
    /// Builds the whole forest of instance `idx` from the master secret.
    pub fn new(pp: &Pp, master: &MasterSecret, idx: u64) -> Self {
        let mut starts = vec![[0u8; N]; COORDS * SUPERS * SUBS * CHILDREN * CHILD_CHAINS];
        let mut sub = vec![Vec::new(); COORDS * SUPERS * SUBS];
        let mut top = vec![Vec::new(); COORDS];
        let mut key = [[[0u8; N]; 2]; COORDS];
        for c in 0..COORDS {
            let mut supers = Vec::with_capacity(SUPERS);
            for s in 0..SUPERS {
                let mut tops = [[[0u8; N]; 2]; SUBS];
                for j in 0..SUBS {
                    let leaves: Vec<Digest> = (0..CHILDREN)
                        .map(|a| {
                            let secrets = child_secrets(pp, master, idx, c, s, j, a);
                            for (i, &start) in secrets.iter().enumerate() {
                                starts[chain_index(c, s, j, a, i)] = start;
                            }
                            let ends = std::array::from_fn(|i| {
                                forest_chain(pp, idx, c, s, j, a, i, 0, CHAIN_TOP, secrets[i])
                            });
                            child_leaf(pp, idx, c, s, j, a, &ends)
                        })
                        .collect();
                    let levels = fold_levels(SUB_HEIGHT, leaves, |level, node, left, right| {
                        sub_node(pp, idx, c, s, j, level, node, left, right)
                    });
                    tops[j] = [levels[SUB_HEIGHT - 1][0], levels[SUB_HEIGHT - 1][1]];
                    sub[sub_index(c, s, j)] = levels;
                }
                supers.push(super_child(pp, idx, c, s, &tops));
            }
            let levels = fold_levels(TOP_HEIGHT, supers, |level, node, left, right| {
                top_node(pp, idx, c, level, node, left, right)
            });
            key[c] = [levels[TOP_HEIGHT - 1][0], levels[TOP_HEIGHT - 1][1]];
            top[c] = levels;
        }
        Self { starts, sub, top, key }
    }

    pub fn key(&self) -> &ForestKey {
        &self.key
    }

    /// The opening of every coordinate at the digest's marks.
    pub fn open(&self, pp: &Pp, idx: u64, marks: &[CoordMark; COORDS]) -> ForestOpening {
        std::array::from_fn(|c| {
            let mark = marks[c];
            let s = mark.super_child;
            CoordOpening {
                sub: std::array::from_fn(|j| {
                    let (a, word) = (mark.child[j], lut(mark.word[j]));
                    let values = std::array::from_fn(|i| {
                        let start = self.starts[chain_index(c, s, j, a, i)];
                        forest_chain(pp, idx, c, s, j, a, i, 0, CHAIN_TOP - word[i] as usize, start)
                    });
                    let levels = &self.sub[sub_index(c, s, j)];
                    SubOpening { values, path: std::array::from_fn(|level| levels[level][(a >> level) ^ 1]) }
                }),
                top: std::array::from_fn(|level| self.top[c][level][(s >> level) ^ 1]),
            }
        })
    }
}

/// The levels of a Merkle tree over `leaves`, hashed up to level `height - 1` (two nodes): the root
/// is never hashed.
fn fold_levels(
    height: usize, leaves: Vec<Digest>, node: impl Fn(usize, usize, &Digest, &Digest) -> Digest,
) -> Levels {
    let mut levels = vec![leaves];
    for level in 0..height - 1 {
        let below = &levels[level];
        let up = (0..below.len() / 2).map(|j| node(level, j, &below[2 * j], &below[2 * j + 1])).collect();
        levels.push(up);
    }
    levels
}

/// The levels of a Merkle tree, level 0 being its leaves.
type Levels = Vec<Vec<Digest>>;

/// `Fts.recover`: the forest key an opening reaches.
pub fn forest_recover(
    pp: &Pp, idx: u64, marks: &[CoordMark; COORDS], opening: &ForestOpening,
) -> ForestKey {
    std::array::from_fn(|c| {
        let (mark, open) = (marks[c], &opening[c]);
        let s = mark.super_child;
        let tops: [[Digest; 2]; SUBS] = std::array::from_fn(|j| {
            let (a, word) = (mark.child[j], lut(mark.word[j]));
            let ends = std::array::from_fn(|i| {
                let deficit = word[i] as usize;
                forest_chain(pp, idx, c, s, j, a, i, CHAIN_TOP - deficit, deficit, open.sub[j].values[i])
            });
            let leaf = child_leaf(pp, idx, c, s, j, a, &ends);
            let node = (0..SUB_HEIGHT - 1).fold(leaf, |current, level| {
                let sibling = open.sub[j].path[level];
                let (left, right) =
                    if (a >> level) & 1 == 1 { (sibling, current) } else { (current, sibling) };
                sub_node(pp, idx, c, s, j, level, a >> (level + 1), &left, &right)
            });
            order_tops((a >> (SUB_HEIGHT - 1)) & 1 == 1, node, open.sub[j].path[SUB_HEIGHT - 1])
        });
        let super_node = super_child(pp, idx, c, s, &tops);
        let node = (0..TOP_HEIGHT - 1).fold(super_node, |current, level| {
            let sibling = open.top[level];
            let (left, right) = if (s >> level) & 1 == 1 { (sibling, current) } else { (current, sibling) };
            top_node(pp, idx, c, level, s >> (level + 1), &left, &right)
        });
        order_tops((s >> (TOP_HEIGHT - 1)) & 1 == 1, node, open.top[TOP_HEIGHT - 1])
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table is the rule of `LeanForest/Scheme.lean::codewordCodes`: its first entries as base-5
    /// numbers, its composition by digit pattern, and the 42 codewords listed twice.
    #[test]
    fn codeword_table_matches_the_rule() {
        let table = codeword_table();
        let code = |d: &[u8; CHILD_CHAINS]| {
            d.iter().enumerate().map(|(i, &x)| x as usize * 5usize.pow((5 - i) as u32)).sum::<usize>()
        };
        let first: Vec<usize> = table[..16].iter().map(code).collect();
        assert_eq!(first, vec![9, 21, 29, 45, 101, 105, 129, 145, 225, 501, 505, 525, 629, 645, 725, 1125]);
        for d in table.iter() {
            assert_eq!(d.iter().map(|&x| x as usize).sum::<usize>(), CODEWORD_SUM);
            assert!(d.iter().all(|&x| x as usize <= CHAIN_TOP));
        }
        let distinct: std::collections::BTreeSet<_> = table.iter().collect();
        assert_eq!(distinct.len(), 214, "246 codewords, the 32 most spread-out left out");
        let twice = table.len() - distinct.len();
        assert_eq!(twice, 42, "the 42 most concentrated appear twice");
        // sorted by decreasing sum of squares
        let squares: Vec<u32> = table[..214].iter().map(|d| d.iter().map(|&x| (x as u32).pow(2)).sum()).collect();
        assert!(squares.windows(2).all(|w| w[0] >= w[1]));
    }

    /// One instance of the forest costs `8 * 7390` Keccak-f permutations (and the same count of
    /// calls, weighted by their blocks, with the other hashes), and an opening carries 22 values per
    /// coordinate and costs 20 calls per coordinate to recover.
    #[test]
    fn forest_costs() {
        let master = [9u8; MASTER_SECRET_LEN];
        for hash in HashFn::ALL {
            let pp = Pp::new(hash, [5u8; PUBLIC_PARAM_LEN]);
            let c = |payload: usize| hash.call(payload);
            let before = compressions();
            let forest = Forest::new(&pp, &master, 3);
            // per child 3 derivations, 24 chain steps and a leaf; per sub-tree 6 nodes; per
            // super-child 1 hash; per coordinate 14 top nodes.
            let child = (CHILD_CHAINS / 2) as u64 * c(MASTER_SECRET_LEN)
                + (CHILD_CHAINS * CHAIN_TOP) as u64 * c(N)
                + c(CHILD_CHAINS * N);
            let expected = COORDS as u64
                * (SUPERS as u64 * (SUBS as u64 * (CHILDREN as u64 * child + 6 * c(2 * N)) + c(4 * N)) + 14 * c(2 * N));
            assert_eq!(compressions() - before, expected, "{hash:?}");
            if hash == HashFn::Keccak256 {
                assert_eq!(expected, 59_120);
            }

            let marks: [CoordMark; COORDS] = std::array::from_fn(|c| CoordMark {
                super_child: c % SUPERS,
                child: [c % 8, (c + 3) % 8],
                word: [c as u8, 200],
            });
            let opening = forest.open(&pp, 3, &marks);
            let before = compressions();
            assert_eq!(forest_recover(&pp, 3, &marks, &opening), forest.key);
            let per_coord = SUBS as u64 * (CODEWORD_SUM as u64 * c(N) + c(CHILD_CHAINS * N) + 2 * c(2 * N))
                + c(4 * N)
                + 3 * c(2 * N);
            assert_eq!(compressions() - before, COORDS as u64 * per_coord, "{hash:?}");
            if hash == HashFn::Keccak256 {
                assert_eq!(per_coord, 20);
            }
            assert_eq!(VALUES_PER_COORD, 22);

            let mut bad = opening;
            bad[2].sub[1].values[0][0] ^= 1;
            assert_ne!(forest_recover(&pp, 3, &marks, &bad), forest.key);
        }
    }
}
