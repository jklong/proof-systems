use crate::nolookup::scalars::{ProofEvaluations};
use crate::nolookup::constraints::{eval_zk_polynomial};
use ark_ff::{FftField, Field, Zero, One};
use ark_poly::{univariate::DensePolynomial, Evaluations, EvaluationDomain, Radix2EvaluationDomain as D};
use crate::gate::{GateType, CurrOrNext};
use std::ops::{Add, Sub, Mul, Neg};
use std::collections::{HashMap, HashSet};
use std::fmt;
use CurrOrNext::*;
use rayon::prelude::*;

use crate::wires::COLUMNS;
use crate::domains::EvaluationDomains;

/// The collection of constants required to evaluate an `Expr`.
pub struct Constants<F> {
    /// The challenge alpha from the PLONK IOP.
    pub alpha: F,
    /// The challenge beta from the PLONK IOP.
    pub beta: F,
    /// The challenge gamma from the PLONK IOP.
    pub gamma: F,
    /// The challenge joint_combiner which is used to combine
    /// joint lookup tables.
    pub joint_combiner: F,
}

/// The polynomials specific to the lookup argument.
///
/// All are evaluations over the D8 domain
pub struct LookupEnvironment<'a, F: FftField> {
    /// The sorted lookup table polynomials.
    pub sorted: &'a Vec<Evaluations<F, D<F>>>,
    /// The lookup aggregation polynomials.
    pub aggreg: &'a Evaluations<F, D<F>>,
    /// The lookup-type selector polynomials.
    pub selectors: &'a Vec<Evaluations<F, D<F>>>,
    /// The evaluations of the combined lookup table polynomial.
    pub table: &'a Evaluations<F, D<F>>,
}

/// The collection of polynomials (all in evaluation form) and constants
/// required to evaluate an expression as a polynomial.
///
/// All are evaluations.
pub struct Environment<'a, F : FftField> {
    /// The witness column polynomials
    pub witness: &'a [Evaluations<F, D<F>>; COLUMNS],
    /// The coefficient column polynomials
    pub coefficient: &'a [Evaluations<F, D<F>>; COLUMNS],
    /// The polynomial which vanishes on the last 3 elements of the domain.
    /// Used for ZK blinding.
    pub zk_polynomial: &'a Evaluations<F, D<F>>,
    /// The permutation aggregation polynomial.
    pub z: &'a Evaluations<F, D<F>>,
    /// The index selector polynomials.
    pub index: HashMap<GateType, &'a Evaluations<F, D<F>>>,
    /// The value `prod_{j != 1} (1 - omega^j)`, used for efficiently
    /// computing the evaluations of the unnormalized Lagrange basis polynomials.
    pub l0_1: F,
    /// Constant values required
    pub constants: Constants<F>,
    /// The domains used in the PLONK argument.
    pub domain: EvaluationDomains<F>,
    /// Lookup specific polynomials
    pub lookup: Option<LookupEnvironment<'a, F>>,
}

impl<'a, F: FftField> Environment<'a, F> {
    fn get_column(&self, col: &Column) -> Option<&'a Evaluations<F, D<F>>> {
        use Column::*;
        let lookup = self.lookup.as_ref();
        match col {
            Witness(i) => Some(&self.witness[*i]),
            Coefficient(i) => Some(&self.coefficient[*i]),
            Z => Some(&self.z),
            LookupKindIndex(i) => lookup.map(|l| &l.selectors[*i]),
            LookupSorted(i) => lookup.map(|l| &l.sorted[*i]),
            LookupAggreg => lookup.map(|l| l.aggreg),
            LookupTable => lookup.map(|l| l.table),
            Index(t) =>
                match self.index.get(t) {
                    None => return None,
                    Some(e) => Some(e),
                }
        }
    }
}

// In this file, we define
//
// l_i(x) to be the unnormalized lagrange polynomial,
// (x^n - 1) / (x - omega^i)
// = prod_{j != i} (x - omega^j)
//
// and L_i(x) to be the normalized lagrange polynomial,
// L_i(x) = l_i(x) / l_i(omega^i)

/// Computes `prod_{j != 1} (1 - omega^j)`
pub fn l0_1<F:FftField>(d: D<F>) -> F {
    let mut omega_j = d.group_gen;
    let mut res = F::one();
    for _ in 1..(d.size as usize) {
        res *= F::one() - omega_j;
        omega_j *= d.group_gen;
    }
    res
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// A type representing one of the polynomials involved in the PLONK IOP.
pub enum Column {
    Witness(usize),
    Z,
    LookupSorted(usize),
    LookupAggreg,
    LookupTable,
    LookupKindIndex(usize),
    Index(GateType),
    Coefficient(usize),
}

impl Column {
    fn domain(&self) -> Domain {
        match self {
            _ => Domain::D8,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
/// A type representing a variable which can appear in a constraint. It specifies a column
/// and a relative position (Curr or Next)
pub struct Variable {
    /// The column of this variable
    pub col: Column,
    /// The row (Curr of Next) of this variable
    pub row: CurrOrNext,
}

#[derive(Clone, Debug, PartialEq)]
/// An arithmetic expression over
///
/// - the operations *, +, -, ^
/// - the constants `alpha`, `beta`, `gamma`, `joint_combiner`, and literal field elements.
pub enum ConstantExpr<F> {
    // TODO: Factor these out into an enum just for Alpha, Beta, Gamma, JointCombiner
    Alpha,
    Beta,
    Gamma,
    JointCombiner,
    Literal(F),
    Pow(Box<ConstantExpr<F>>, usize),
    // TODO: I think having separate Add, Sub, Mul constructors is faster than
    // having a BinOp constructor :(
    Add(Box<ConstantExpr<F>>, Box<ConstantExpr<F>>),
    Mul(Box<ConstantExpr<F>>, Box<ConstantExpr<F>>),
    Sub(Box<ConstantExpr<F>>, Box<ConstantExpr<F>>),
}

impl<F: Copy> ConstantExpr<F> {
    fn to_polish_(&self, res: &mut Vec<PolishToken<F>>) {
        match self {
            ConstantExpr::Alpha => {
                res.push(PolishToken::Alpha)
            },
            ConstantExpr::Beta => {
                res.push(PolishToken::Beta)
            },
            ConstantExpr::Gamma => {
                res.push(PolishToken::Gamma)
            },
            ConstantExpr::JointCombiner => {
                res.push(PolishToken::JointCombiner)
            },
            ConstantExpr::Add(x, y) => {
                x.as_ref().to_polish_(res);
                y.as_ref().to_polish_(res);
                res.push(PolishToken::Add)
            },
            ConstantExpr::Mul(x, y) => {
                x.as_ref().to_polish_(res);
                y.as_ref().to_polish_(res);
                res.push(PolishToken::Mul)
            },
            ConstantExpr::Sub(x, y) => {
                x.as_ref().to_polish_(res);
                y.as_ref().to_polish_(res);
                res.push(PolishToken::Sub)
            },
            ConstantExpr::Literal(x) => {
                res.push(PolishToken::Literal(*x))
            },
            ConstantExpr::Pow(x, n) => {
                x.to_polish_(res);
                res.push(PolishToken::Pow(*n))
            },
        }
    }
}

impl<F: Field> ConstantExpr<F> {
    /// Exponentiate a constant expression.
    pub fn pow(self, p: usize) -> Self {
        if p == 0 {
            return Literal(F::one());
        }
        use ConstantExpr::*;
        match self {
            Literal(x) => Literal(x.pow(&[p as u64])),
            x => Pow(Box::new(x), p)
        }
    }

    /// Evaluate the given constant expression to a field element.
    pub fn value(&self, c: &Constants<F>) -> F {
        use ConstantExpr::*;
        match self {
            Alpha => c.alpha,
            Beta => c.beta,
            Gamma => c.gamma,
            JointCombiner => c.joint_combiner,
            Literal(x) => *x,
            Pow(x, p) => x.value(c).pow(&[*p as u64]),
            Mul(x, y) => x.value(c) * y.value(c),
            Add(x, y) => x.value(c) + y.value(c),
            Sub(x, y) => x.value(c) - y.value(c),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CacheId(usize);

pub struct Cache {
    next_id: usize
}

impl Cache {
    pub fn new() -> Self {
        Cache { next_id: 0 }
    }

    fn next_id(&mut self) -> CacheId {
        let id = self.next_id;
        self.next_id += 1;
        CacheId(id)
    }

    pub fn cache<C>(&mut self, e: Expr<C>) -> Expr<C> {
        Expr::Cache(self.next_id(), Box::new(e))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Op2 {
    Add,
    Mul,
    Sub,
}

impl Op2 {
    fn to_polish<A>(&self) -> PolishToken<A> {
        use Op2::*;
        match self {
            Add => PolishToken::Add,
            Mul => PolishToken::Mul,
            Sub => PolishToken::Sub,
        }
    }
}

/// An multi-variate polynomial over the base ring `C` with
/// variables
///
/// - `Cell(v)` for `v : Variable`
/// - ZkPolynomial
/// - UnnormalizedLagrangeBasis(i) for `i : usize`
///
/// This represents a PLONK "custom constraint", which enforces that
/// the corresponding combination of the polynomials corresponding to
/// the above variables should vanish on the PLONK domain.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr<C> {
    Constant(C),
    Cell(Variable),
    BinOp(Op2, Box<Expr<C>>, Box<Expr<C>>),
    ZkPolynomial,
    /// UnnormalizedLagrangeBasis(i) is
    /// (x^n - 1) / (x - omega^i)
    UnnormalizedLagrangeBasis(usize),
    Pow(Box<Expr<C>>, usize),
    Cache(CacheId, Box<Expr<C>>),
}

/// For efficiency of evaluation, we compile expressions to
/// [reverse Polish notation](https://en.wikipedia.org/wiki/Reverse_Polish_notation)
/// expressions, which are vectors of the below tokens.
#[derive(Clone, Debug, PartialEq)]
pub enum PolishToken<F> {
    Alpha,
    Beta,
    Gamma,
    JointCombiner,
    Literal(F),
    Cell(Variable),
    Pow(usize),
    Add,
    Mul,
    Sub,
    ZkPolynomial,
    UnnormalizedLagrangeBasis(usize),
    Store,
    Load(usize),
}

fn evaluate_variable<'a, 'b, 'c, F: Field>(evals: &'a [ProofEvaluations<F>], v: &'b Variable) -> Result<F, &'c str> {
    let evals = &evals[curr_or_next(v.row)];
    use Column::*;
    let l = evals.lookup.as_ref().ok_or("Lookup should not have been used");
    match v.col {
        Witness(i) => Ok(evals.w[i]),
        Z => Ok(evals.z),
        LookupSorted(i) => l.map(|l| l.sorted[i]),
        LookupAggreg => l.map(|l| l.aggreg),
        LookupTable => l.map(|l| l.table),
        Index(GateType::Poseidon) => Ok(evals.poseidon_selector),
        Index(GateType::Generic) => Ok(evals.generic_selector),
        Coefficient(_) | LookupKindIndex(_) | Index(_) =>
            Err("Cannot get index evaluation (should have been linearized away)")
    }
}

impl<F: FftField> PolishToken<F> {
    /// Evaluate an RPN expression to a field element.
    pub fn evaluate<'c>(
        toks: &Vec<PolishToken<F>>, d: D<F>, pt: F,
        evals: &[ProofEvaluations<F>], c: &Constants<F>) -> Result<F, &'c str> {
        let mut stack = vec![];
        let mut cache : Vec<F> = vec![];

        for t in toks.iter() {
            use PolishToken::*;
            match t {
                Alpha => stack.push(c.alpha),
                Beta => stack.push(c.beta),
                Gamma => stack.push(c.gamma),
                JointCombiner => stack.push(c.joint_combiner),
                ZkPolynomial => stack.push(eval_zk_polynomial(d, pt)),
                UnnormalizedLagrangeBasis(i) =>
                    stack.push(d.evaluate_vanishing_polynomial(pt) / (pt - d.group_gen.pow(&[*i as u64]))),
                Literal(x) => stack.push(*x),
                Cell(v) =>
                    match evaluate_variable(evals, v) {
                        Ok(x) => stack.push(x),
                        Err(e) => return Err(e)
                    },
                Pow(n) => {
                    let i = stack.len() - 1;
                    stack[i] = stack[i].pow(&[*n as u64]);
                },
                Add => {
                    let y = stack.pop().ok_or("Empty stack")?;
                    let x = stack.pop().ok_or("Empty stack")?;
                    stack.push(x + y);
                },
                Mul => {
                    let y = stack.pop().ok_or("Empty stack")?;
                    let x = stack.pop().ok_or("Empty stack")?;
                    stack.push(x * y);
                },
                Sub => {
                    let y = stack.pop().ok_or("Empty stack")?;
                    let x = stack.pop().ok_or("Empty stack")?;
                    stack.push(x - y);
                },
                Store => {
                    let x = stack[stack.len() - 1];
                    cache.push(x);
                },
                Load(i) => {
                    stack.push(cache[*i])
                },
            }
        }

        assert_eq!(stack.len(), 1);
        Ok(stack[0])
    }
}

impl<C> Expr<C> {
    /// Convenience function for constructing cell variables.
    pub fn cell(col:Column, row: CurrOrNext) -> Expr<C> {
        Expr::Cell(Variable { col, row })
    }

    /// Convenience function for constructing constant expressions.
    pub fn constant(c: C) -> Expr<C> {
        Expr::Constant(c)
    }

    fn degree(&self, d1_size: usize) -> usize {
        use Expr::*;
        match self {
            Constant(_) => 0,
            ZkPolynomial => 3,
            UnnormalizedLagrangeBasis(_) => d1_size,
            Cell(_) => d1_size,
            BinOp(Op2::Mul, x, y) => (*x).degree(d1_size) + (*y).degree(d1_size),
            BinOp(Op2::Add, x, y) | BinOp(Op2::Sub, x, y) => std::cmp::max((*x).degree(d1_size), (*y).degree(d1_size)),
            Pow(e, d) => d * e.degree(d1_size),
            Cache(_, e) => e.degree(d1_size)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, FromPrimitive, ToPrimitive)]
enum Domain {
    D1 = 1, D2 = 2, D4 = 4, D8 = 8
}

#[derive(Clone)]
enum EvalResult<'a, F: FftField> {
    Constant(F),
    Evals { domain: Domain, evals: Evaluations<F, D<F>> },
    SubEvals { domain: Domain, shift: usize, evals : &'a Evaluations<F, D<F>> }
}

/// Compute the powers of `x`, `x^0, ..., x^{n - 1}`
pub fn pows<F: Field>(x: F, n : usize) -> Vec<F> {
    if n == 0 {
        return vec![F::one()];
    } else if n == 1 {
        return vec![F::one(), x];
    }
    let mut v = vec![F::one(), x];
    for i in 2..n {
        v.push(v[i - 1] * x);
    }
    v
}

// Compute the evaluations of the unnormalized lagrange polynomial on
// H_8 or H_4. Taking H_8 as an example, we show how to compute this
// polynomial on the expanded domain.
//
// Let H = < omega >, |H| = n.
//
// Let l_i(x) be the unnormalized lagrange polynomial,
// (x^n - 1) / (x - omega^i)
// = prod_{j != i} (x - omega^j)
//
// For h in H, h != omega^i,
// l_i(h) = 0.
// l_i(omega^i) 
// = prod_{j != i} (omega^i - omega^j)
// = omega^{i (n - 1)} * prod_{j != i} (1 - omega^{j - i})
// = omega^{i (n - 1)} * prod_{j != 0} (1 - omega^j)
// = omega^{i (n - 1)} * l_0(1)
// = omega^{i n} * omega^{-i} * l_0(1)
// = omega^{-i} * l_0(1)
//
// So it is easy to compute l_i(omega^i) from just l_0(1).
//
// Also, consider the expanded domain H_8 generated by
// an 8nth root of unity omega_8 (where H_8^8 = H).
//
// Let omega_8^k in H_8. Write k = 8 * q + r with r < 8.
// Then
// omega_8^k = (omega_8^8)^q * omega_8^r = omega^q * omega_8^r
//
// l_i(omega_8^k)
// = (omega_8^{k n} - 1) / (omega_8^k - omega^i)
// = (omega^{q n} omega_8^{r n} - 1) / (omega_8^k - omega^i)
// = ((omega_8^n)^r - 1) / (omega_8^k - omega^i)
// = ((omega_8^n)^r - 1) / (omega^q omega_8^r - omega^i)
fn unnormalized_lagrange_evals<F:FftField>(
    l0_1: F, 
    i: usize, 
    res_domain: Domain,
    env: &Environment<F>) -> Evaluations<F, D<F>> {

    let k =
        match res_domain {
            Domain::D1 => 1,
            Domain::D2 => 2,
            Domain::D4 => 4,
            Domain::D8 => 8,
        };
    let res_domain = get_domain(res_domain, env);

    let d1 = env.domain.d1;
    let n = d1.size;
    let ii = i as u64;
    assert!(ii < n);
    let omega = d1.group_gen;
    let omega_i = omega.pow(&[ii]);
    let omega_minus_i = omega.pow(&[n - ii]);

    // Write res_domain = < omega_k > with
    // |res_domain| = k * |H|

    // omega_k^0, ..., omega_k^k
    let omega_k_n_pows = pows(res_domain.group_gen.pow(&[n]), k);
    let omega_k_pows = pows(res_domain.group_gen, k);

    let mut evals : Vec<F> = {
        let mut v = vec![F::one(); k*(n as usize)];
        let mut omega_q = F::one();
        for q in 0..(n as usize) {
            // omega_q == omega^q
            for r in 1..k {
                v[k * q + r] = omega_q * omega_k_pows[r] - omega_i;
            }
            omega_q *= omega;
        }
        ark_ff::fields::batch_inversion::<F>(&mut v[..]);
        v
    };
    // At this point, in the 0 mod k indices, we have dummy values,
    // and in the other indices k*q + r, we have 
    // 1 / (omega^q omega_k^r - omega^i)

    // Set the 0 mod k indices
    for q in 0..(n as usize) {
        evals[k * q] = F::zero();
    }
    evals[k * i] = omega_minus_i * l0_1;

    // Finish computing the non-zero mod k indices
    for q in 0..(n as usize) {
        for r in 1..k {
            evals[k * q + r] *= omega_k_n_pows[r] - F::one();
        }
    }

    Evaluations::<F, D<F>>::from_vec_and_domain(
        evals,
        res_domain
    )
}

impl<'a, F: FftField> EvalResult<'a, F> {
    fn init_<G: Sync + Send + Fn(usize) -> F>(
        res_domain: (Domain, D<F>),
        g : G) -> Evaluations<F, D<F>> {
        let n = res_domain.1.size as usize;
        Evaluations::<F, D<F>>::from_vec_and_domain(
            (0..n).into_par_iter().map(g).collect(),
            res_domain.1
        )
    }

    fn init<G: Sync + Send + Fn(usize) -> F>(res_domain: (Domain, D<F>), g : G) -> Self {
        Self::Evals {
            domain: res_domain.0,
            evals: Self::init_(res_domain, g)
        }
    }

    fn add<'b, 'c>(self, other: EvalResult<'b, F>, res_domain: (Domain, D<F>)) -> EvalResult<'c, F> {
        use EvalResult::*;
        match (self, other) {
            (Constant(x), Constant(y)) => Constant(x + y),
            (Evals { domain, mut evals }, Constant(x))
            | (Constant(x), Evals { domain, mut evals }) => {
                evals.evals.par_iter_mut().for_each(|e| *e += x);
                Evals { domain, evals }
            },
            (SubEvals { evals, domain: d, shift:s }, Constant(x)) |
            (Constant(x), SubEvals { evals, domain: d, shift:s }) => {
                let n = res_domain.1.size as usize;
                let scale = (d as usize) / (res_domain.0 as usize);
                assert!(scale != 0);
                let v: Vec<_> = (0..n).into_par_iter().map(|i| {
                    x + evals.evals[(scale * i + (d as usize) * s) % evals.evals.len()]
                }).collect();
                Evals {
                    domain: res_domain.0,
                    evals:
                        Evaluations::<F, D<F>>::from_vec_and_domain(
                            v,
                            res_domain.1
                        )
                }
            },
            (Evals { domain:d1, evals: mut es1 }, Evals { domain:d2, evals: es2 }) => {
                assert_eq!(d1, d2);
                es1 += &es2;
                Evals { domain: d1, evals: es1 }
            },
            (SubEvals { domain: d_sub, shift: s, evals: es_sub }, Evals { domain: d, mut evals })
            | (Evals { domain: d, mut evals }, SubEvals { domain: d_sub, shift: s, evals: es_sub }) => {
                let scale = (d_sub as usize) / (d as usize);
                assert!(scale != 0);
                evals.evals.par_iter_mut().enumerate().for_each(|(i, e)| {
                    *e += es_sub.evals[(scale * i + (d_sub as usize) * s) % es_sub.evals.len()];
                });
                Evals { evals, domain: d }
            },
            (SubEvals { domain: d1, shift: s1, evals: es1 }, SubEvals { domain: d2, shift: s2, evals: es2 }) => {
                let scale1 = (d1 as usize) / (res_domain.0 as usize);
                assert!(scale1 != 0);
                let scale2 = (d2 as usize) / (res_domain.0 as usize);
                assert!(scale2 != 0);

                let n = res_domain.1.size as usize;
                let v: Vec<_> = (0..n).into_par_iter().map(|i| {
                    es1.evals[(scale1 * i + (d1 as usize) * s1) % es1.evals.len()] 
                        + es2.evals[(scale2 * i + (d2 as usize) * s2) % es2.evals.len()]
                }).collect();

                Evals {
                    domain: res_domain.0,
                    evals:
                        Evaluations::<F, D<F>>::from_vec_and_domain(
                            v,
                            res_domain.1
                        )
                }
            }
        }
    }

    fn sub<'b, 'c>(self, other: EvalResult<'b, F>, res_domain: (Domain, D<F>)) -> EvalResult<'c, F> {
        use EvalResult::*;
        match (self, other) {
            (Constant(x), Constant(y)) => Constant(x - y),
            (Evals { domain, mut evals }, Constant(x)) => {
                evals.evals.par_iter_mut().for_each(|e| *e -= x);
                Evals { domain, evals }
            },
            (Constant(x), Evals { domain, mut evals }) => {
                evals.evals.par_iter_mut().for_each(|e| *e = x - *e);
                Evals { domain, evals }
            },
            (SubEvals { evals, domain: d, shift:s }, Constant(x)) => {
                let scale = (d as usize) / (res_domain.0 as usize);
                assert!(scale != 0);
                EvalResult::init(
                    res_domain,
                    |i| evals.evals[(scale * i + (d as usize) * s) % evals.evals.len()] - x)
            },
            (Constant(x), SubEvals { evals, domain: d, shift:s }) => {
                let scale = (d as usize) / (res_domain.0 as usize);
                assert!(scale != 0);
                EvalResult::init(
                    res_domain,
                    |i| x - evals.evals[(scale * i + (d as usize) * s) % evals.evals.len()])
            },
            (Evals { domain:d1, evals: mut es1 }, Evals { domain:d2, evals: es2 }) => {
                assert_eq!(d1, d2);
                es1 -= &es2;
                Evals { domain: d1, evals: es1 }
            },
            (SubEvals { domain: d_sub, shift: s, evals: es_sub }, Evals { domain: d, mut evals }) => {
                let scale = (d_sub as usize) / (d as usize);
                assert!(scale != 0);
                evals.evals.par_iter_mut().enumerate().for_each(|(i, e)| {
                    *e = es_sub.evals[(scale * i + (d_sub as usize) * s) % es_sub.evals.len()] - *e;
                });
                Evals { evals, domain: d }
            }
            (Evals { domain: d, mut evals }, SubEvals { domain: d_sub, shift: s, evals: es_sub }) => {
                let scale = (d_sub as usize) / (d as usize);
                assert!(scale != 0);
                evals.evals.par_iter_mut().enumerate().for_each(|(i, e)| {
                    *e -= es_sub.evals[(scale * i + (d_sub as usize) * s) % es_sub.evals.len()];
                });
                Evals { evals, domain: d }
            },
            (SubEvals { domain: d1, shift: s1, evals: es1 }, SubEvals { domain: d2, shift: s2, evals: es2 }) => {
                let scale1 = (d1 as usize) / (res_domain.0 as usize);
                assert!(scale1 != 0);
                let scale2 = (d2 as usize) / (res_domain.0 as usize);
                assert!(scale2 != 0);

                EvalResult::init(
                    res_domain,
                    |i| es1.evals[(scale1 * i + (d1 as usize) * s1) % es1.evals.len()]
                    - es2.evals[(scale2 * i + (d2 as usize) * s2) % es2.evals.len()])
            }
        }
    }

    fn pow<'b>(self, d: usize, res_domain: (Domain, D<F>)) -> EvalResult<'b, F> {
        let mut acc = EvalResult::Constant(F::one());
        for i in (0..64).rev() {
            acc = acc.square(res_domain);

            if (d >> i) & 1 == 1 {
                // TODO: Avoid the unnecessary cloning
                acc = acc.mul(self.clone(), res_domain)
            }
        }
        acc
    }

    fn square(self, res_domain: (Domain, D<F>)) -> Self {
        use EvalResult::*;
        match self {
            Constant(x) => Constant(x.square()),
            Evals { domain, mut evals } => {
                evals.evals.par_iter_mut().for_each(|e| {
                    e.square_in_place();
                });
                Evals { domain, evals }
            },
            SubEvals { evals, domain: d, shift:s } => {
                let scale = (d as usize) / (res_domain.0 as usize);
                assert!(scale != 0);
                Self::init(
                    res_domain,
                    |i| evals.evals[(scale * i + (d as usize) * s) % evals.evals.len()].square())
            },
        }
    }

    /*
    fn mul_ref(self, other: &Self, res_domain: (Domain, D<F>)) -> Self {
        use EvalResult::*;
        match (self, other) {
            (Constant(x), Constant(y)) => Constant(x * y),
            (Evals { domain, mut evals }, Constant(x)) => {
                evals.evals.par_iter_mut().for_each(|e| *e *= x);
                Evals { domain, evals }
            }
            (Constant(x), Evals { domain, evals }) => {
                Self::init(
                    res_domain,
                    |i| x * evals.evals[i])
            },
            (SubEvals { evals, domain: d, shift:s }, &Constant(x))
            | (Constant(x), &SubEvals { evals, domain: d, shift:s }) => {
                let scale = (d as usize) / (res_domain.0 as usize);
                Self::init(
                    res_domain,
                    |i| x * evals.evals[(scale * i + (d as usize) * s) % evals.evals.len()])
            },
            (Evals { domain:d1, evals: mut es1 }, &Evals { domain:d2, evals: es2 }) => {
                assert_eq!(d1, d2);
                es1 *= &es2;
                Evals { domain: d1, evals: es1 }
            },
            (Evals { domain: d, mut evals }, &SubEvals { domain: d_sub, shift: s, evals: es_sub }) => {
                let scale = (d_sub as usize) / (d as usize);
                evals.evals.par_iter_mut().enumerate().for_each(|(i, e)| {
                    *e *= es_sub.evals[(scale * i + (d_sub as usize) * s) % es_sub.evals.len()];
                });
                Evals { evals, domain: d }
            },
            (SubEvals { domain: d_sub, shift: s, evals: es_sub }, &Evals { domain: d, evals }) => {
                let scale = (d_sub as usize) / (d as usize);
                Self::init(
                    res_domain,
                    |i| evals.evals[i] * es_sub.evals[(scale * i + (d_sub as usize) * s) % es_sub.evals.len()])
            },
            (SubEvals { domain: d1, shift: s1, evals: es1 }, &SubEvals { domain: d2, shift: s2, evals: es2 }) => {
                let scale1 = (d1 as usize) / (res_domain.0 as usize);
                let scale2 = (d2 as usize) / (res_domain.0 as usize);

                Self::init(
                    res_domain,
                    |i| es1.evals[(scale1 * i + (d1 as usize) * s1) % es1.evals.len()] * es2.evals[(scale2 * i + (d2 as usize) * s2) % es1.evals.len()])
            }
        }
    } */

    fn mul<'b, 'c>(self, other: EvalResult<'b, F>, res_domain: (Domain, D<F>)) -> EvalResult<'c, F> {
        use EvalResult::*;
        match (self, other) {
            (Constant(x), Constant(y)) => Constant(x * y),
            (Evals { domain, mut evals }, Constant(x))
            | (Constant(x), Evals { domain, mut evals }) => {
                evals.evals.par_iter_mut().for_each(|e| *e *= x);
                Evals { domain, evals }
            },
            (SubEvals { evals, domain: d, shift:s }, Constant(x)) |
            (Constant(x), SubEvals { evals, domain: d, shift:s }) => {
                let scale = (d as usize) / (res_domain.0 as usize);
                assert!(scale != 0);
                EvalResult::init(
                    res_domain,
                    |i| x * evals.evals[(scale * i + (d as usize) * s) % evals.evals.len()])
            },
            (Evals { domain:d1, evals: mut es1 }, Evals { domain:d2, evals: es2 }) => {
                assert_eq!(d1, d2);
                es1 *= &es2;
                Evals { domain: d1, evals: es1 }
            },
            (SubEvals { domain: d_sub, shift: s, evals: es_sub }, Evals { domain: d, mut evals })
            | (Evals { domain: d, mut evals }, SubEvals { domain: d_sub, shift: s, evals: es_sub }) => {
                let scale = (d_sub as usize) / (d as usize);
                assert!(scale != 0);
                evals.evals.par_iter_mut().enumerate().for_each(|(i, e)| {
                    *e *= es_sub.evals[(scale * i + (d_sub as usize) * s) % es_sub.evals.len()];
                });
                Evals { evals, domain: d }
            },
            (SubEvals { domain: d1, shift: s1, evals: es1 }, SubEvals { domain: d2, shift: s2, evals: es2 }) => {
                let scale1 = (d1 as usize) / (res_domain.0 as usize);
                assert!(scale1 != 0);
                let scale2 = (d2 as usize) / (res_domain.0 as usize);
                assert!(scale2 != 0);

                EvalResult::init(
                    res_domain,
                    |i| es1.evals[(scale1 * i + (d1 as usize) * s1) % es1.evals.len()] * es2.evals[(scale2 * i + (d2 as usize) * s2) % es1.evals.len()])
            }
        }
    }

}

/*
fn eval_result_op<'a, 'b, 'c, F: FftField>(op: Op2, dom: (Domain, D<F>), x: EvalResult<'a, F>, y: EvalResult<'b, F>) -> EvalResult<'c, F> {
    match op {
        Op2::Mul => x.mul(y, dom),
        Op2::Add => x.add(y, dom),
        Op2::Sub => x.sub(y, dom),
    }
}
*/

fn get_domain<F: FftField>(d: Domain, env: &Environment<F>) -> D<F> {
    match d {
        Domain::D1 => env.domain.d1,
        Domain::D2 => env.domain.d2,
        Domain::D4 => env.domain.d4,
        Domain::D8 => env.domain.d8
    }
}

fn curr_or_next(row: CurrOrNext) -> usize {
    match row {
        Curr => 0,
        Next => 1
    }
}

impl<F: FftField> Expr<ConstantExpr<F>> {
    /// Convenience function for constructing expressions from literal
    /// field elements.
    pub fn literal(x: F) -> Self {
        Expr::Constant(ConstantExpr::Literal(x))
    }

    /// Compile an expression to an RPN expression.
    pub fn to_polish(&self) -> Vec<PolishToken<F>> {
        let mut res = vec![];
        let mut cache = HashMap::new();
        self.to_polish_(&mut cache, &mut res);
        res
    }

    fn to_polish_(&self, cache: &mut HashMap<CacheId, usize>, res: &mut Vec<PolishToken<F>>) {
        match self {
            Expr::Pow(x, d) => {
                x.to_polish_(cache, res);
                res.push(PolishToken::Pow(*d))
            },
            Expr::Constant(c) => {
                c.to_polish_(res);
            },
            Expr::Cell(v) => {
                res.push(PolishToken::Cell(*v))
            },
            Expr::ZkPolynomial => {
                res.push(PolishToken::ZkPolynomial);
            },
            Expr::UnnormalizedLagrangeBasis(i) => {
                res.push(PolishToken::UnnormalizedLagrangeBasis(*i));
            },
            Expr::BinOp(op, x, y) => {
                x.to_polish_(cache, res);
                y.to_polish_(cache, res);
                res.push(op.to_polish());
            },
            Expr::Cache(id, e) => {
                match cache.get(id) {
                    Some(pos) =>
                        // Already computed and stored this.
                        res.push(PolishToken::Load(*pos)),
                    None => {
                        // Haven't computed this yet. Compute it, then store it.
                        e.to_polish_(cache, res);
                        res.push(PolishToken::Store);
                        cache.insert(*id, cache.len());
                    }
                }
            },
        }
    }

    /// Combines multiple constraints `[c0, ..., cn]` into a single constraint
    /// `alpha^alpha0 * c0 + alpha^{alpha0 + 1} * c1 + ... + alpha^{alpha0 + n} * cn`.
    pub fn combine_constraints(alpha0: usize, cs: Vec<Self>) -> Self {
        let zero = Expr::<ConstantExpr<F>>::zero();
        cs.into_iter().zip(alpha0..).map(|(c, i)| {
            Expr::Constant(ConstantExpr::Alpha.pow(i)) * c
        }).fold(zero, |acc, x| acc + x)
    }

    /// The expression `beta`.
    pub fn beta() -> Self {
        Expr::Constant(ConstantExpr::Beta)
    }

    fn evaluate_constants_(&self, c: &Constants<F>) -> Expr<F> {
        use Expr::*;
        // TODO: Use cache
        match self {
            Pow(x, d) => x.evaluate_constants_(c).pow(*d),
            Constant(x) => Constant(x.value(c)),
            Cell(v) => Cell(*v),
            ZkPolynomial => ZkPolynomial,
            UnnormalizedLagrangeBasis(i) => UnnormalizedLagrangeBasis(*i),
            BinOp(Op2::Add, x, y) => x.evaluate_constants_(c) + y.evaluate_constants_(c),
            BinOp(Op2::Mul, x, y) => x.evaluate_constants_(c) * y.evaluate_constants_(c),
            BinOp(Op2::Sub, x, y) => x.evaluate_constants_(c) - y.evaluate_constants_(c),
            Cache(id, e) => Cache(*id, Box::new(e.evaluate_constants_(c))),
        }
    }

    /// Evaluate an expression as a field element against an environment.
    pub fn evaluate(
        &self, d: D<F>, pt: F,
        evals: &[ProofEvaluations<F>],
        env: &Environment<F>) -> Result<F, &str> {
        self.evaluate_(d, pt, evals, &env.constants)
    }

    /// Evaluate an expression as a field element against the constants.
    pub fn evaluate_(
        &self, d: D<F>, pt: F,
        evals: &[ProofEvaluations<F>],
        c: &Constants<F>) -> Result<F, &str> {
        use Expr::*;
        match self {
            Constant(x) => Ok(x.value(c)),
            Pow(x, p) => Ok(x.evaluate_(d, pt, evals, c)?.pow(&[*p as u64])),
            BinOp(Op2::Mul, x, y) => {
                let x = (*x).evaluate_(d, pt, evals, c)?;
                let y = (*y).evaluate_(d, pt, evals, c)?;
                Ok(x * y)
            },
            BinOp(Op2::Add, x, y) => {
                let x = (*x).evaluate_(d, pt, evals, c)?;
                let y = (*y).evaluate_(d, pt, evals, c)?;
                Ok(x + y)
            },
            BinOp(Op2::Sub, x, y) => {
                let x = (*x).evaluate_(d, pt, evals, c)?;
                let y = (*y).evaluate_(d, pt, evals, c)?;
                Ok(x - y)
            },
            ZkPolynomial => Ok(eval_zk_polynomial(d, pt)),
            UnnormalizedLagrangeBasis(i) =>
                Ok(d.evaluate_vanishing_polynomial(pt) / (pt - d.group_gen.pow(&[*i as u64]))),
            Cell(v) => evaluate_variable(evals, v),
            Cache(_, e) => e.evaluate_(d, pt, evals, c),
        }
    }

    /// Evaluate the constant expressions in this expression down into field elements.
    pub fn evaluate_constants(&self, env: &Environment<F>) -> Expr<F> {
        self.evaluate_constants_(&env.constants)
    }

    /// Compute the polynomial corresponding to this expression, in evaluation form.
    pub fn evaluations<'a>(&self, env: &Environment<'a, F>) -> Evaluations<F, D<F>> {
        self.evaluate_constants(env).evaluations(env)
    }
}

enum Either<A, B> {
    Left(A),
    Right(B)
}

impl<F: FftField> Expr<F> {
    /// Evaluate an expression into a field element.
    pub fn evaluate(
        &self, d: D<F>, pt: F,
        evals: &[ProofEvaluations<F>]) -> Result<F, &str> {
        use Expr::*;
        match self {
            Constant(x) => Ok(*x),
            Pow(x, p) => Ok(x.evaluate(d, pt, evals)?.pow(&[*p as u64])),
            BinOp(Op2::Mul, x, y) => {
                let x = (*x).evaluate(d, pt, evals)?;
                let y = (*y).evaluate(d, pt, evals)?;
                Ok(x * y)
            },
            BinOp(Op2::Add, x, y) => {
                let x = (*x).evaluate(d, pt, evals)?;
                let y = (*y).evaluate(d, pt, evals)?;
                Ok(x + y)
            },
            BinOp(Op2::Sub, x, y) => {
                let x = (*x).evaluate(d, pt, evals)?;
                let y = (*y).evaluate(d, pt, evals)?;
                Ok(x - y)
            },
            ZkPolynomial => Ok(eval_zk_polynomial(d, pt)),
            UnnormalizedLagrangeBasis(i) => 
                Ok(d.evaluate_vanishing_polynomial(pt) / (pt - d.group_gen.pow(&[*i as u64]))),
            Cell(v) => evaluate_variable(evals, v),
            Cache(_, e) => e.evaluate(d, pt, evals),
        }
    }

    /// Compute the polynomial corresponding to this expression, in evaluation form.
    pub fn evaluations<'a>(&self, env: &Environment<'a, F>) -> Evaluations<F, D<F>> {
        let d1_size = env.domain.d1.size as usize;
        let deg = self.degree(d1_size);
        let d =
            if deg <= d1_size {
                Domain::D1
            } else if deg <= 4 * d1_size {
                Domain::D4
            } else if deg <= 8 * d1_size {
                Domain::D8
            } else {
                panic!("constraint had degree {} > 8", deg);
            };

        let mut cache = HashMap::new();

        let evals =
            match self.evaluations_helper(&mut cache, d, env) {
                Either::Left(x) => x,
                Either::Right(id) => cache.get(&id).unwrap().clone(),
            };

        match evals {
            EvalResult::Evals { evals, domain } => {
                assert_eq!(domain, d);
                evals
            },
            EvalResult::Constant(x) => 
                EvalResult::init_((d, get_domain(d, env)), |_| x),
            EvalResult::SubEvals { evals, domain: d_sub, shift: s } => {
                let res_domain = get_domain(d, env);
                let scale = (d_sub as usize) / (d as usize);
                assert!(scale != 0);
                EvalResult::init_(
                    (d, res_domain),
                    |i| evals.evals[(scale * i + (d_sub as usize) * s) % evals.evals.len()])
            }
        }
    }

    fn evaluations_helper<'a, 'b>(
        &self,
        cache: &'b mut HashMap<CacheId, EvalResult<'a, F>>,
        d: Domain,
        env: & Environment<'a, F>) -> Either<EvalResult<'a, F>, CacheId> where 'a: 'b {

        let get = |cache: &'b HashMap<CacheId, EvalResult<'a, F>>, id: &CacheId| -> Option<EvalResult<'b, F>> {
            cache.get(id).map(|e| {
                match e {
                    EvalResult::Constant(x) => EvalResult::Constant(*x),
                    EvalResult::SubEvals { domain, shift, evals } =>
                        EvalResult::SubEvals { domain: *domain, shift: *shift, evals },
                    EvalResult::Evals { domain, evals } =>
                        EvalResult::SubEvals { domain: *domain, shift: 0, evals }
                }
            })
        };

        let res : EvalResult<'a, F> =
            match self {
                Expr::Cache(id, e) => {
                    match cache.get(id) {
                        Some(_) => {
                            return Either::Right(*id) },
                        None => {
                            match e.evaluations_helper(cache, d, env) {
                                Either::Left(es) => {
                                    cache.insert(*id, es);
                                },
                                Either::Right(_) => {}
                            };
                            return Either::Right(*id)
                        }
                    }
                },
                Expr::Pow(x, p) => {
                    let x = x.evaluations_helper(cache, d, env);
                    match x {
                        Either::Left(x) => x.pow(*p, (d, get_domain(d, env))),
                        Either::Right(id) => get(cache, &id).unwrap().pow(*p, (d, get_domain(d, env))),
                    }
                },
                Expr::ZkPolynomial =>
                    EvalResult::SubEvals { 
                        domain: Domain::D8,
                        shift: 0,
                        evals: env.zk_polynomial
                    },
                Expr::Constant(x) => {
                    EvalResult::Constant(*x)
                },
                Expr::UnnormalizedLagrangeBasis(i) =>
                    EvalResult::Evals {
                        domain: d,
                        evals: unnormalized_lagrange_evals(env.l0_1, *i, d, env)
                    },
                Expr::Cell(Variable { col, row }) => {
                    let evals : &'a Evaluations<F, D<F>> = {
                        match env.get_column(col) {
                            None => return Either::Left(EvalResult::Constant(F::zero())),
                            Some(e) => e
                        }
                    };
                    EvalResult::SubEvals { 
                        domain: col.domain(),
                        shift: curr_or_next(*row),
                        evals
                    }
                },
                Expr::BinOp(op, e1, e2) => {
                    let dom = (d, get_domain(d, env));
                    let f = |x: EvalResult<F>, y: EvalResult<F>| {
                        match op {
                            Op2::Mul => x.mul(y, dom),
                            Op2::Add => x.add(y, dom),
                            Op2::Sub => x.sub(y, dom),
                        }
                    };
                    let e1 = e1.evaluations_helper(cache, d, env);
                    let e2 = e2.evaluations_helper(cache, d, env);
                    use Either::*;
                    match (e1, e2) {
                        (Left(e1), Left(e2)) => f(e1, e2),
                        (Right(id1), Left(e2)) => f(get(cache, &id1).unwrap(), e2),
                        (Left(e1), Right(id2)) => f(e1, get(cache, &id2).unwrap()),
                        (Right(id1), Right(id2)) => f(get(cache, &id1).unwrap(), get(cache, &id2).unwrap()),
                    }
                },
            };
        Either::Left(res)
    }
}

#[derive(Clone, Debug)]
/// A "linearization", which is linear combination with `E` coefficients of
/// columns.
pub struct Linearization<E> {
    pub constant_term: E,
    pub index_terms: Vec<(Column, E)>
}

impl<A> Linearization<A> {
    /// Apply a function to all the coefficients in the linearization.
    pub fn map<B, F: Fn(&A) -> B>(&self, f: F) -> Linearization<B> {
        Linearization {
            constant_term: f(&self.constant_term),
            index_terms: self.index_terms.iter().map(|(c, x)| (*c, f(x))).collect()
        }
    }
}

impl<F: FftField> Linearization<Expr<ConstantExpr<F>>> {
    /// Evaluate the constants in a linearization with `ConstantExpr<F>` coefficients down
    /// to literal field elements.
    pub fn evaluate_constants(&self, env: &Environment<F>) -> Linearization<Expr<F>> {
        self.map(|e| e.evaluate_constants(env))
    }
}

impl<F: FftField> Linearization<Vec<PolishToken<F>>> {
    /// Given a linearization and an environment, compute the polynomial corresponding to the
    /// linearization, in evaluation form.
    pub fn to_polynomial(&self, env: &Environment<F>, pt: F, evals: &[ProofEvaluations<F>]) -> (F, DensePolynomial<F>) {
        let cs = &env.constants;
        let n = env.domain.d1.size as usize;
        let mut res = vec![F::zero(); n];
        self.index_terms.iter().for_each(|(idx, c)| {
            let c = PolishToken::evaluate(c, env.domain.d1, pt, evals, &cs).unwrap();
            let e = env.get_column(&idx).expect(&format!("Index polynomial {:?} not found", idx));
            let scale = e.evals.len() / n;
            res.par_iter_mut().enumerate().for_each(|(i, r)| {
                *r += c * e.evals[scale * i]
            })
        });
        let p = Evaluations::<F, D<F>>::from_vec_and_domain(res, env.domain.d1).interpolate();
        (PolishToken::evaluate(&self.constant_term, env.domain.d1, pt, evals, &cs).unwrap(), p)
    }
}

impl<F: FftField> Linearization<Expr<ConstantExpr<F>>> {
    /// Given a linearization and an environment, compute the polynomial corresponding to the
    /// linearization, in evaluation form.
    pub fn to_polynomial(&self, env: &Environment<F>, pt: F, evals: &[ProofEvaluations<F>]) -> (F, DensePolynomial<F>) {
        let cs = &env.constants;
        let n = env.domain.d1.size as usize;
        let mut res = vec![F::zero(); n];
        self.index_terms.iter().for_each(|(idx, c)| {
            let c = c.evaluate_(env.domain.d1, pt, evals, &cs).unwrap();
            let e = env.get_column(&idx).expect(&format!("Index polynomial {:?} not found", idx));
            let scale = e.evals.len() / n;
            res.par_iter_mut().enumerate().for_each(|(i, r)| {
                *r += c * e.evals[scale * i]
            })
        });
        let p = Evaluations::<F, D<F>>::from_vec_and_domain(res, env.domain.d1).interpolate();
        (self.constant_term.evaluate_(env.domain.d1, pt, evals, &cs).unwrap(), p)
    }
}

impl<F: One> Expr<F> {
    /// Exponentiate an expression
    pub fn pow(self, p: usize) -> Self {
        use Expr::*;
        if p == 0 {
            return Constant(F::one());
        }
        Pow(Box::new(self), p)
    }
}

type Monomials<F> = HashMap<Vec<Variable>, Expr<F>>;

fn mul_monomials<F: Neg<Output=F> + Clone + One + Zero + PartialEq>(
    e1: &Monomials<F>,
    e2: &Monomials<F>) -> Monomials<F> {
    let mut res : HashMap<_, Expr<F>> = HashMap::new();
    for (m1, c1) in e1.iter() {
        for (m2, c2) in e2.iter() {
            let mut m = m1.clone();
            m.extend(m2);
            m.sort();
            let c1c2 = c1.clone() * c2.clone();
            let v = res.entry(m).or_insert(Expr::<F>::zero());
            *v = v.clone() + c1c2;
        }
    }
    res
}

impl<F: Neg<Output=F> + Clone + One + Zero + PartialEq> Expr<F> {
    fn monomials(&self) -> HashMap<Vec<Variable>, Expr<F>> {
        let sing = |v: Vec<Variable>, c: Expr<F>| {
            let mut h = HashMap::new();
            h.insert(v, c);
            h
        };
        let constant = |e : Expr<F>| sing(vec![], e);
        use Expr::*;
        match self {
            Pow(x, d) => {
                // Run the multiplication logic with square and multiply
                let mut acc = sing(vec![], Expr::<F>::one());
                let mut acc_is_one = true;
                let x = x.monomials();

                for i in (0..64).rev() {
                    if !acc_is_one {
                        let acc2 = mul_monomials(&acc, &acc);
                        acc = acc2;
                    }

                    if (d >> i) & 1 == 1 {
                        let res = mul_monomials(&acc, &x);
                        acc = res;
                        acc_is_one = false;
                    }
                }
                acc
            },
            Cache(_, e) => e.monomials(),
            UnnormalizedLagrangeBasis(i) => constant(UnnormalizedLagrangeBasis(*i)),
            ZkPolynomial => constant(ZkPolynomial),
            Constant(c) => constant(Constant(c.clone())),
            Cell(var) => sing(vec![*var], Constant(F::one())),
            BinOp(Op2::Add, e1, e2) => {
                let mut res = e1.monomials();
                for (m, c) in e2.monomials() {
                    let v =
                        match res.remove(&m) {
                            None => c,
                            Some(v) => v + c
                        };
                    res.insert(m, v);
                }
                res
            },
            BinOp(Op2::Sub, e1, e2) => {
                let mut res = e1.monomials();
                for (m, c) in e2.monomials() {
                    let v =
                        match res.remove(&m) {
                            None => -c, // Expr::constant(F::one()) * c,
                            Some(v) => v - c
                        };
                    res.insert(m, v);
                }
                res
            },
            BinOp(Op2::Mul, e1, e2) => {
                let e1 = e1.monomials();
                let e2 = e2.monomials();
                mul_monomials(&e1, &e2)
            }
        }
    }

    /// There is an optimization in PLONK called "linearization" in which a certain
    /// polynomial is expressed as a linear combination of other polynomials in order
    /// to reduce the number of evaluations needed in the IOP (by relying on the homomorphic
    /// property of the polynomial commitments used.)
    ///
    /// The function performs this "linearization", which we now describe in some detail.
    ///
    /// In mathematical language, an expression `e: Expr<F>`
    /// is an element of the polynomial ring `F[V]`, where `V` is a set of variables.
    ///
    /// Given a subset `V_0` of `V` (and letting `V_1 = V \setminus V_0`), there is a map
    /// `factor_{V_0}: F[V] -> (F[V_1])[V_0]`. That is, polynomials with `F` coefficients in the variables `V = V_0 \cup V_1`
    /// are the same thing as polynomials with `F[V_1]` coefficients in variables `V_0`.
    ///
    /// There is also a function
    /// `lin_or_err : (F[V_1])[V_0] -> Result<Vec<(V_0, F[V_2])>, &str>`
    ///
    /// which checks if the given input is in fact a degree 1 polynomial in the variables `V_0`
    /// (i.e., a linear combination of `V_0` elements with `F[V_1]` coefficients)
    /// returning this linear combination if so.
    ///
    /// Given an expression `e` and set of columns `C_0`, letting
    /// `V_0 = { Variable { col: c, row: r } | c in C_0, r in { Curr, Next } }`,
    /// this function computes `lin_or_err(factor_{V_0}(e))`, although it does not
    /// compute it in that way. Instead, it computes it by reducing the expression into
    /// a sum of monomials with `F` coefficients, and then factors the monomials.
    pub fn linearize(&self, evaluated: HashSet<Column>) -> Result<Linearization<Expr<F>>, &str> {
        let mut res : HashMap<Column, Expr<F>> = HashMap::new();
        let mut constant_term : Expr<F> = Self::zero();
        let monomials = self.monomials();

        for (m, c) in monomials {
            let (evaluated, mut unevaluated) : (Vec<_>, _) = m.into_iter().partition(|v| evaluated.contains(&v.col));
            let c = evaluated.into_iter().fold(c, |acc, v| acc * Expr::Cell(v));
            if unevaluated.len() == 0 {
                constant_term = constant_term + c;
            } else if unevaluated.len() == 1 {
                let var = unevaluated.remove(0);
                match var.row {
                    Next => return Err("Linearization failed (needed polynomial value at \"next\" row)"),
                    Curr => {
                        let e =
                            match res.remove(&var.col) {
                                Some(v) => v + c,
                                None => c
                            };
                        res.insert(var.col, e);
                        // This code used to be
                        //
                        // let v = res.entry(var.col).or_insert(0.into());
                        // *v = v.clone() + c
                        //
                        // but calling clone made it extremely slow, so I replaced it
                        // with the above that moves v out of the map with .remove and
                        // into v + c.
                        //
                        // I'm not sure if there's a way to do it with the HashMap API
                        // without calling remove.
                    }
                }
            }
            else {
                return Err("Linearization failed");
            }
        }
        Ok(Linearization { constant_term, index_terms: res.into_iter().collect() })
    }
}

// Trait implementations

impl<F: Field> Zero for ConstantExpr<F> {
    fn zero() -> Self {
        ConstantExpr::Literal(F::zero())
    }

    fn is_zero(&self) -> bool {
        match self {
            ConstantExpr::Literal(x) => x.is_zero(),
            _ => false
        }
    }
}

impl<F: Field> One for ConstantExpr<F> {
    fn one() -> Self {
        ConstantExpr::Literal(F::one())
    }

    fn is_one(&self) -> bool {
        match self {
            ConstantExpr::Literal(x) => x.is_one(),
            _ => false
        }
    }
}

impl<F : One + Neg<Output=F>> Neg for ConstantExpr<F> {
    type Output = ConstantExpr<F>;

    fn neg(self) -> ConstantExpr<F> {
        match self {
            ConstantExpr::Literal(x) => ConstantExpr::Literal(x.neg()),
            e => ConstantExpr::Mul(Box::new(ConstantExpr::Literal(F::one().neg())), Box::new(e))
        }
    }
}

impl<F: Field> Add<ConstantExpr<F>> for ConstantExpr<F> {
    type Output = ConstantExpr<F>;
    fn add(self, other: Self) -> Self {
        use ConstantExpr::*;
        if self.is_zero() {
            return other;
        }
        if other.is_zero() {
            return self
        }
        match (self, other) {
            (Literal(x), Literal(y)) => Literal(x + y),
            (x, y) => Add(Box::new(x), Box::new(y))
        }
    }
}

impl<F: Field> Sub<ConstantExpr<F>> for ConstantExpr<F> {
    type Output = ConstantExpr<F>;
    fn sub(self, other: Self) -> Self {
        use ConstantExpr::*;
        if other.is_zero() {
            return self
        }
        match (self, other) {
            (Literal(x), Literal(y)) => Literal(x - y),
            (x, y) => Sub(Box::new(x), Box::new(y))
        }
    }
}

impl<F: Field> Mul<ConstantExpr<F>> for ConstantExpr<F> {
    type Output = ConstantExpr<F>;
    fn mul(self, other: Self) -> Self {
        use ConstantExpr::*;
        if self.is_one() {
            return other;
        }
        if other.is_one() {
            return self;
        }
        match (self, other) {
            (Literal(x), Literal(y)) => Literal(x * y),
            (x, y) => Mul(Box::new(x), Box::new(y))
        }
    }
}

impl<F: Zero> Zero for Expr<F> {
    fn zero() -> Self {
        Expr::Constant(F::zero())
    }

    fn is_zero(&self) -> bool {
        match self {
            Expr::Constant(x) => x.is_zero(),
            _ => false
        }
    }
}

impl<F: One + PartialEq> One for Expr<F> {
    fn one() -> Self {
        Expr::Constant(F::one())
    }

    fn is_one(&self) -> bool {
        match self {
            Expr::Constant(x) => x.is_one(),
            _ => false
        }
    }
}

impl<F : One + Neg<Output=F>> Neg for Expr<F> {
    type Output = Expr<F>;

    fn neg(self) -> Expr<F> {
        match self {
            Expr::Constant(x) => Expr::Constant(x.neg()),
            e => Expr::BinOp(Op2::Mul, Box::new(Expr::Constant(F::one().neg())), Box::new(e))
        }
    }
}

impl<F: Zero> Add<Expr<F>> for Expr<F> {
    type Output = Expr<F>;
    fn add(self, other: Self) -> Self {
        if self.is_zero() {
            return other;
        }
        if other.is_zero() {
            return self;
        }
        Expr::BinOp(Op2::Add, Box::new(self), Box::new(other))
    }
}

impl<F: One + PartialEq> Mul<Expr<F>> for Expr<F> {
    type Output = Expr<F>;
    fn mul(self, other: Self) -> Self {
        if self.is_one() {
            return other;
        }
        if other.is_one() {
            return self;
        }
        Expr::BinOp(Op2::Mul, Box::new(self), Box::new(other))
    }
}

impl<F: Zero> Sub<Expr<F>> for Expr<F> {
    type Output = Expr<F>;
    fn sub(self, other: Self) -> Self {
        if other.is_zero() {
            return self;
        }
        Expr::BinOp(Op2::Sub, Box::new(self), Box::new(other))
    }
}

impl<F: Field> From<u64> for Expr<F> {
    fn from(x : u64) -> Self {
        Expr::Constant(F::from(x))
    }
}

impl<F: Field> From<u64> for Expr<ConstantExpr<F>> {
    fn from(x : u64) -> Self {
        Expr::Constant(ConstantExpr::Literal(F::from(x)))
    }
}

impl<F: fmt::Display> fmt::Display for ConstantExpr<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ConstantExpr::*;
        match self {
            Alpha => write!(f, "Alpha")?,
            Beta => write!(f, "Beta")?,
            Gamma => write!(f, "Gamma")?,
            JointCombiner => write!(f, "JointCombiner")?,
            Literal(x) => write!(f, "{}", x)?,
            Pow(x, n) => write!(f, "Pow({}, {})", x.as_ref(), n)?,
            Add(x, y) => write!(f, "({} + {})", x.as_ref(), y.as_ref())?,
            Mul(x, y) => write!(f, "({} * {})", x.as_ref(), y.as_ref())?,
            Sub(x, y) => write!(f, "({} - {})", x.as_ref(), y.as_ref())?,
        };
        Ok(())
    }
}

impl<F: fmt::Display> fmt::Display for Expr<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Expr::*;
        match self {
            Constant(x) => write!(f, "{}", x)?,
            Cell(v) => write!(f, "Cell({:?})", *v)?,
            UnnormalizedLagrangeBasis(i) => write!(f, "UnnormalizedLagrangeBasis({})", *i)?,
            ZkPolynomial => write!(f, "ZkPolynomial")?,
            BinOp(Op2::Add, x, y) => write!(f, "({} + {})", x.as_ref(), y.as_ref())?,
            BinOp(Op2::Mul, x, y) => write!(f, "({} * {})", x.as_ref(), y.as_ref())?,
            BinOp(Op2::Sub, x, y) => write!(f, "({} - {})", x.as_ref(), y.as_ref())?,
            Pow(x, d) => write!(f, "({}^{})", x.as_ref(), d)?,
            Cache(_, e) => e.fmt(f)?
        };
        Ok(())
    }
}

/// An alias for the intended usage of the expression type in constructing constraints.
pub type E<F> = Expr<ConstantExpr<F>>;