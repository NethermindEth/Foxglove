module

public import Foxglove.Interp.Bernoulli.Basic
public import VCVio.OracleComp.OracleComp

@[expose] public section
namespace Foxglove

namespace Interp

/-- An oracle spec whose operations can be implemented by Bernoulli coin flips. -/
class OracleBernoulliInterpretable {α : Type} (oSpec : OracleSpec α) where
  interp_op (op : oSpec.toPFunctor.A) : BernoulliM (oSpec.toPFunctor.B op)

/-- Rejection sampling from `m` upwards: uniform on `{m, …, n - 1}` (`split'_spec`). -/
def split' {n : ℕ} (m : Fin n) : BernoulliM (Fin n) := do
  if h₁ : n = m.1 + 1
    then pure m
    else
      let b ← flip
        ⟨
          (mkRat 1 (n - m.1) : ℝ),
          by
            simp only [Set.mem_Icc, Rat.cast_nonneg, zero_le_one, Rat.mkRat_nonneg, true_and]
            norm_cast
            refine Rat.num_le_denom_iff.mp ?_
            unfold mkRat
            split_ifs with h
            · simp
            · simp only [Rat.num_normalize, isUnit_one, Int.natAbs_of_isUnit, Fin.is_le',
              isUnit_iff_eq_one, IsUnit.dvd, Nat.gcd_sub_left_right_of_dvd, Nat.gcd_one_left,
              Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
              Rat.den_normalize, Nat.div_one, Nat.cast_sub]
              omega⟩
      if b
        then pure m
        else split' (⟨m.1 + 1, (by omega)⟩ : Fin n)
termination_by n - m.1
decreasing_by have := m.isLt; omega

/-- A uniform sample from `Fin (n + 1)`: the Bernoulli implementation of `unifSpec`'s oracle. -/
def split (n : ℕ) : BernoulliM (Fin (n + 1)) :=
  split' (0 : Fin (n + 1))

instance : OracleBernoulliInterpretable unifSpec where
  interp_op := split

open OracleBernoulliInterpretable in
instance {α β} {oSpec₁ : OracleSpec α} {oSpec₂ : OracleSpec β} [OracleBernoulliInterpretable oSpec₁]
    [OracleBernoulliInterpretable oSpec₂]
  : OracleBernoulliInterpretable (oSpec₁ + oSpec₂) where
  interp_op op := match op with
                    | .inl a => interp_op a
                    | .inr a => interp_op a

open OracleBernoulliInterpretable in
def interp {α β} {oSpec : OracleSpec β} [OracleBernoulliInterpretable oSpec] (p : OracleComp oSpec α)
      : BernoulliM α :=
  match p with
   | PFunctor.FreeM.pure a => pure a
   | PFunctor.FreeM.liftBind op f => bind (interp_op op) (fun x => interp (f x))

instance {α} {oSpec : OracleSpec α} [OracleBernoulliInterpretable oSpec] :
  BernoulliInterpretable (OracleComp oSpec) where
    interp := interp

open OracleBernoulliInterpretable in
/-- `interp` is a monad morphism, by induction on the free monad: the `wp` rules for `pure`
and `>>=` apply to `OracleComp` programs directly. -/
instance {α} {oSpec : OracleSpec α} [OracleBernoulliInterpretable oSpec] :
    LawfulBernoulliInterpretable (OracleComp oSpec) where
  interp_pure _ := rfl
  interp_bind t f := by
    induction t with
    | pure a => rfl
    | queryBind op k ih =>
      show (interp_op op >>= fun x ↦ BernoulliInterpretable.interp (k x >>= f))
        = (interp_op op >>= fun x ↦ BernoulliInterpretable.interp (k x))
          >>= fun a ↦ BernoulliInterpretable.interp (f a)
      simp only [ih, bind_assoc]

end Interp

end Foxglove
