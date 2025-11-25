-- Falfia's First Proofs for Kindergarteners
import LeanLTL

namespace LeanLTL.Examples

open LeanLTL
open scoped LeanLTL.Notation

noncomputable section
namespace Falfia
axiom σ : Type*
axiom n : σ → ℤ

-- If n is always > 5, then n must always be > 4
example {σ : Type} (n : σ → ℕ) : ⊨ⁱ LLTL[𝐆 ((← n) > 5) → 𝐆 ((← n) > 4)] := by
  simp +contextual [push_ltl]
  intros t ht q n'
  specialize q n'
  omega

-- If at the start of the trace n is 1, and it always increases by 1 every
-- timestep, then it's always > 0
example : ⊨ⁱ LLTL[((← n) = 1 ∧ 𝐆 ((𝐗 (← n)) = (← n) + 1)) → 𝐆 ((← n) > 0)] := by
  simp +contextual [push_ltl]
  intros t t_inf start next n
  induction n
  case zero =>
    rw [start]
    trivial
  case succ n ih =>
    specialize next n
    rw [Nat.add_comm n 1, next]
    omega
