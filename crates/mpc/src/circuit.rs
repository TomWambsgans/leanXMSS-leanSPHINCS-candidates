//! Boolean circuits with statically typed wires, compiled into a level-by-level program.
//!
//! A wire is a compile-time constant, public (known to all parties, possibly different in every
//! instance of a batch), or secret (shared). Constants fold away at build time; public-public gates
//! run in the clear; a secret XOR, NOT, or AND with a public wire is local. Only secret-secret ANDs
//! cost communication, and the program runs them level by level: one round per AND level.
//!
//! The ripple-carry and carry-save adders of [`crate::blake2s_circuit`] follow the gadgets of
//! leanVM's flock (crates/flock/src/gf2.rs, CREDIT: https://github.com/succinctlabs/flock,
//! MIT OR Apache-2.0).

pub type Wire = u32;
pub const ZERO: Wire = 0;
pub const ONE: Wire = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Const,
    Pub,
    Sec,
}

#[derive(Clone, Copy, Debug)]
enum Node {
    Const(bool),
    PubIn(u32),
    SecIn(u32),
    Xor(Wire, Wire),
    And(Wire, Wire),
    Not(Wire),
}

#[derive(Default)]
pub struct Builder {
    nodes: Vec<Node>,
    kinds: Vec<Kind>,
    n_pub_inputs: u32,
    n_sec_inputs: u32,
    outputs: Vec<Wire>,
}

impl Builder {
    pub fn new() -> Self {
        let mut b = Self::default();
        b.push(Node::Const(false), Kind::Const);
        b.push(Node::Const(true), Kind::Const);
        b
    }

    fn push(&mut self, node: Node, kind: Kind) -> Wire {
        self.nodes.push(node);
        self.kinds.push(kind);
        (self.nodes.len() - 1) as Wire
    }

    pub fn kind(&self, w: Wire) -> Kind {
        self.kinds[w as usize]
    }

    pub fn constant(&self, bit: bool) -> Wire {
        if bit { ONE } else { ZERO }
    }

    pub fn pub_input(&mut self) -> Wire {
        self.n_pub_inputs += 1;
        self.push(Node::PubIn(self.n_pub_inputs - 1), Kind::Pub)
    }

    pub fn sec_input(&mut self) -> Wire {
        self.n_sec_inputs += 1;
        self.push(Node::SecIn(self.n_sec_inputs - 1), Kind::Sec)
    }

    pub fn not(&mut self, a: Wire) -> Wire {
        match self.nodes[a as usize] {
            Node::Const(v) => self.constant(!v),
            Node::Not(x) => x,
            _ => self.push(Node::Not(a), self.kind(a)),
        }
    }

    pub fn xor(&mut self, a: Wire, b: Wire) -> Wire {
        if a == b {
            return ZERO;
        }
        for (c, x) in [(a, b), (b, a)] {
            if let Node::Const(v) = self.nodes[c as usize] {
                return if v { self.not(x) } else { x };
            }
        }
        let kind = self.kind(a).max(self.kind(b));
        self.push(Node::Xor(a, b), kind)
    }

    pub fn and(&mut self, a: Wire, b: Wire) -> Wire {
        if a == b {
            return a;
        }
        for (c, x) in [(a, b), (b, a)] {
            if let Node::Const(v) = self.nodes[c as usize] {
                return if v { x } else { ZERO };
            }
        }
        let kind = self.kind(a).max(self.kind(b));
        self.push(Node::And(a, b), kind)
    }

    /// Marks a secret wire as an output, in order.
    pub fn output(&mut self, w: Wire) {
        assert_eq!(self.kind(w), Kind::Sec, "outputs are secret wires");
        self.outputs.push(w);
    }

    pub fn compile(&self) -> Program {
        Program::compile(self)
    }
}

/// A local (round-free) operation on slots: public slots hold one bit-vector, secret slots a share.
#[derive(Clone, Copy, Debug)]
pub enum Op {
    PubIn { dst: u32, input: u32 },
    SecIn { dst: u32, input: u32 },
    PubXor { dst: u32, a: u32, b: u32 },
    PubAnd { dst: u32, a: u32, b: u32 },
    PubNot { dst: u32, a: u32 },
    SecXor { dst: u32, a: u32, b: u32 },
    /// Secret `a` XOR public `p`.
    SecXorPub { dst: u32, a: u32, p: u32 },
    /// Secret `a` AND public `p`.
    SecAndPub { dst: u32, a: u32, p: u32 },
    SecNot { dst: u32, a: u32 },
}

/// A secret-secret AND: inputs and output are secret slots.
#[derive(Clone, Copy, Debug)]
pub struct AndOp {
    pub dst: u32,
    pub a: u32,
    pub b: u32,
}

/// The local operations of one level, then the ANDs of the next level (one round).
#[derive(Clone, Debug, Default)]
pub struct Step {
    pub local: Vec<Op>,
    pub ands: Vec<AndOp>,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub steps: Vec<Step>,
    /// Secret slots holding the outputs at the end.
    pub outputs: Vec<u32>,
    pub n_pub_slots: usize,
    pub n_sec_slots: usize,
    pub n_pub_inputs: usize,
    pub n_sec_inputs: usize,
    /// Secret-secret AND gates.
    pub n_and: usize,
    /// AND-depth: the rounds one evaluation takes.
    pub depth: usize,
}

impl Program {
    fn compile(b: &Builder) -> Self {
        let n = b.nodes.len();
        let is_sec_and = |w: usize| matches!(b.nodes[w], Node::And(x, y) if b.kinds[x as usize] == Kind::Sec && b.kinds[y as usize] == Kind::Sec);
        let children = |w: usize| -> Vec<usize> {
            match b.nodes[w] {
                Node::Xor(x, y) | Node::And(x, y) => vec![x as usize, y as usize],
                Node::Not(x) => vec![x as usize],
                _ => vec![],
            }
        };
        // Live nodes, reachable from the outputs.
        let mut live = vec![false; n];
        let mut stack: Vec<usize> = b.outputs.iter().map(|&w| w as usize).collect();
        while let Some(w) = stack.pop() {
            if !live[w] {
                live[w] = true;
                stack.extend(children(w));
            }
        }
        // Levels: a secret-secret AND sits one level above its inputs.
        let mut level = vec![0usize; n];
        for w in 0..n {
            if live[w] {
                let l = children(w).into_iter().map(|c| level[c]).max().unwrap_or(0);
                level[w] = if is_sec_and(w) { l + 1 } else { l };
            }
        }
        let depth = (0..n).filter(|&w| live[w]).map(|w| level[w]).max().unwrap_or(0);
        // Schedule: step l runs the local nodes of level l, then the secret ANDs of level l + 1.
        let mut local_at: Vec<Vec<usize>> = vec![vec![]; depth + 1];
        let mut ands_at: Vec<Vec<usize>> = vec![vec![]; depth + 1];
        for w in 0..n {
            if !live[w] || b.kinds[w] == Kind::Const {
                continue;
            }
            if is_sec_and(w) {
                ands_at[level[w] - 1].push(w);
            } else {
                local_at[level[w]].push(w);
            }
        }
        // Positions in execution order, for liveness: a step's local nodes, then its ANDs' reads
        // (one position), then its ANDs' writes (the next position).
        let mut pos_of_def = vec![usize::MAX; n];
        let mut last_use = vec![0usize; n];
        let mut pos = 0;
        for l in 0..=depth {
            for &w in &local_at[l] {
                for c in children(w) {
                    last_use[c] = last_use[c].max(pos);
                }
                pos_of_def[w] = pos;
                pos += 1;
            }
            for &w in &ands_at[l] {
                for c in children(w) {
                    last_use[c] = last_use[c].max(pos);
                }
            }
            pos += 1;
            for &w in &ands_at[l] {
                pos_of_def[w] = pos;
            }
            pos += 1;
        }
        for &o in &b.outputs {
            last_use[o as usize] = usize::MAX;
        }
        // Slot allocation in execution order; a slot is freed after its value's last use.
        let mut slot = vec![u32::MAX; n];
        let (mut free_pub, mut free_sec): (Vec<u32>, Vec<u32>) = (vec![], vec![]);
        let (mut n_pub_slots, mut n_sec_slots) = (0u32, 0u32);
        let mut frees_at: std::collections::HashMap<usize, Vec<usize>> = Default::default();
        for w in 0..n {
            if live[w] && b.kinds[w] != Kind::Const && last_use[w] != usize::MAX {
                frees_at.entry(last_use[w]).or_default().push(w);
            }
        }
        let mut alloc = |w: usize, slot: &mut Vec<u32>, free_pub: &mut Vec<u32>, free_sec: &mut Vec<u32>| {
            let (free, count) = if b.kinds[w] == Kind::Pub { (free_pub, &mut n_pub_slots) } else { (free_sec, &mut n_sec_slots) };
            slot[w] = free.pop().unwrap_or_else(|| {
                *count += 1;
                *count - 1
            });
        };
        let release = |p: usize, slot: &Vec<u32>, free_pub: &mut Vec<u32>, free_sec: &mut Vec<u32>, frees_at: &std::collections::HashMap<usize, Vec<usize>>| {
            for &w in frees_at.get(&p).into_iter().flatten() {
                if b.kinds[w] == Kind::Pub { free_pub.push(slot[w]) } else { free_sec.push(slot[w]) }
            }
        };
        let mut steps = Vec::with_capacity(depth + 1);
        let mut pos = 0;
        let s = |slot: &Vec<u32>, w: Wire| slot[w as usize];
        for l in 0..=depth {
            let mut step = Step::default();
            for &w in &local_at[l] {
                // The destination may reuse a slot freed by this very node: the ops read before they write.
                release(pos, &slot, &mut free_pub, &mut free_sec, &frees_at);
                alloc(w, &mut slot, &mut free_pub, &mut free_sec);
                let dst = slot[w];
                let op = match b.nodes[w] {
                    Node::PubIn(i) => Op::PubIn { dst, input: i },
                    Node::SecIn(i) => Op::SecIn { dst, input: i },
                    Node::Not(x) if b.kinds[w] == Kind::Pub => Op::PubNot { dst, a: s(&slot, x) },
                    Node::Not(x) => Op::SecNot { dst, a: s(&slot, x) },
                    Node::Xor(x, y) | Node::And(x, y) => {
                        let (kx, ky) = (b.kinds[x as usize], b.kinds[y as usize]);
                        let is_xor = matches!(b.nodes[w], Node::Xor(..));
                        match (kx, ky, is_xor) {
                            (Kind::Pub, Kind::Pub, true) => Op::PubXor { dst, a: s(&slot, x), b: s(&slot, y) },
                            (Kind::Pub, Kind::Pub, false) => Op::PubAnd { dst, a: s(&slot, x), b: s(&slot, y) },
                            (Kind::Sec, Kind::Sec, true) => Op::SecXor { dst, a: s(&slot, x), b: s(&slot, y) },
                            (Kind::Sec, Kind::Pub, true) => Op::SecXorPub { dst, a: s(&slot, x), p: s(&slot, y) },
                            (Kind::Pub, Kind::Sec, true) => Op::SecXorPub { dst, a: s(&slot, y), p: s(&slot, x) },
                            (Kind::Sec, Kind::Pub, false) => Op::SecAndPub { dst, a: s(&slot, x), p: s(&slot, y) },
                            (Kind::Pub, Kind::Sec, false) => Op::SecAndPub { dst, a: s(&slot, y), p: s(&slot, x) },
                            _ => unreachable!("constants are folded, secret ANDs scheduled apart"),
                        }
                    }
                    Node::Const(_) => unreachable!(),
                };
                step.local.push(op);
                pos += 1;
            }
            // The ANDs read all their inputs before any output is written.
            let reads: Vec<(u32, u32)> = ands_at[l]
                .iter()
                .map(|&w| match b.nodes[w] {
                    Node::And(x, y) => (s(&slot, x), s(&slot, y)),
                    _ => unreachable!(),
                })
                .collect();
            release(pos, &slot, &mut free_pub, &mut free_sec, &frees_at);
            pos += 1;
            for (&w, (a, bb)) in ands_at[l].iter().zip(reads) {
                alloc(w, &mut slot, &mut free_pub, &mut free_sec);
                step.ands.push(AndOp { dst: slot[w], a, b: bb });
            }
            release(pos, &slot, &mut free_pub, &mut free_sec, &frees_at);
            pos += 1;
            steps.push(step);
        }
        let n_and = steps.iter().map(|s| s.ands.len()).sum();
        Program {
            steps,
            outputs: b.outputs.iter().map(|&w| slot[w as usize]).collect(),
            n_pub_slots: n_pub_slots as usize,
            n_sec_slots: n_sec_slots as usize,
            n_pub_inputs: b.n_pub_inputs as usize,
            n_sec_inputs: b.n_sec_inputs as usize,
            n_and,
            depth,
        }
    }

    /// Evaluates in the clear, secret inputs given in the clear: the reference for the MPC.
    pub fn eval_plain(&self, words: usize, pub_in: &[Vec<u64>], sec_in: &[Vec<u64>]) -> Vec<Vec<u64>> {
        let mut pubs = vec![vec![0u64; words]; self.n_pub_slots];
        let mut secs = vec![vec![0u64; words]; self.n_sec_slots];
        let ones = vec![u64::MAX; words];
        for step in &self.steps {
            for op in &step.local {
                match *op {
                    Op::PubIn { dst, input } => pubs[dst as usize].copy_from_slice(&pub_in[input as usize]),
                    Op::SecIn { dst, input } => secs[dst as usize].copy_from_slice(&sec_in[input as usize]),
                    Op::PubXor { dst, a, b } => pubs[dst as usize] = zip(&pubs[a as usize], &pubs[b as usize], |x, y| x ^ y),
                    Op::PubAnd { dst, a, b } => pubs[dst as usize] = zip(&pubs[a as usize], &pubs[b as usize], |x, y| x & y),
                    Op::PubNot { dst, a } => pubs[dst as usize] = zip(&pubs[a as usize], &ones, |x, y| x ^ y),
                    Op::SecXor { dst, a, b } => secs[dst as usize] = zip(&secs[a as usize], &secs[b as usize], |x, y| x ^ y),
                    Op::SecXorPub { dst, a, p } => secs[dst as usize] = zip(&secs[a as usize], &pubs[p as usize], |x, y| x ^ y),
                    Op::SecAndPub { dst, a, p } => secs[dst as usize] = zip(&secs[a as usize], &pubs[p as usize], |x, y| x & y),
                    Op::SecNot { dst, a } => secs[dst as usize] = zip(&secs[a as usize], &ones, |x, y| x ^ y),
                }
            }
            let products: Vec<Vec<u64>> = step.ands.iter().map(|g| zip(&secs[g.a as usize], &secs[g.b as usize], |x, y| x & y)).collect();
            for (g, v) in step.ands.iter().zip(products) {
                secs[g.dst as usize] = v;
            }
        }
        self.outputs.iter().map(|&o| secs[o as usize].clone()).collect()
    }
}

fn zip(a: &[u64], b: &[u64], f: impl Fn(u64, u64) -> u64) -> Vec<u64> {
    a.iter().zip(b).map(|(&x, &y)| f(x, y)).collect()
}
