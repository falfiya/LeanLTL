import LeanLTL
import Mathlib
import Mathlib.Data.Set.Basic

namespace LeanLTL.Examples

open LeanLTL
open Classical
open scoped LeanLTL.Notation

noncomputable section
namespace DistributedSystems

structure Process where
  id : ℕ

axiom P : Set Process

namespace CrashFault

structure σ where
  crashed : Set Process

open LeanLTL.Notation

structure Drace where
  t : Trace σ
  inf : t.Infinite
  --crashedForever' : t ⊨ LLTL[∀ p, 𝐆 (p ∈ (← σ.crashed) → 𝐆 p ∈ (← σ.crashed))]
  crashedForever : ∀ n p,
    p ∈ (t.toFun n (by simp [inf])).crashed
    → ∀ n' ≥ n, p ∈ (t.toFun n (by simp [inf])).crashed

-- ?? I LOVE REPEATING MYSELF I LOVE REPEATING MYSELF
def Drace.crashed (t : Drace) (n : ℕ) (p : Process) : Prop :=
  p ∈ (t.t.toFun n (by simp [inf])).crashed

structure Component (𝓇 : Type) (𝒾 : Type) where
  t : Drace
  requestsAt : (t : ℕ) → Process → Set 𝓇
  indicationsAt : (t : ℕ) → Process → Set 𝒾
  noCrashing : ∀ n, ∀ p, t.crashed n p → (requestsAt n p = ∅) ∧ (indicationsAt n p = ∅)

namespace Sync
-- Crash-fault, Synchronous Protocols

axiom DeliverTime : ℕ

namespace FairLossLink
  variable (𝓂 : Type)

  inductive Request | Send (dest : Process) (msg : 𝓂)
  inductive Indication | Deliver (src : Process) (msg : 𝓂)
end FairLossLink

structure FairLossLink (𝓂 : Type) extends Component (FairLossLink.Request 𝓂) (FairLossLink.Indication 𝓂) where
  mk' ::

  fairLoss : ∀ (p₁ p₂ : Process) (msg : 𝓂),
    (∀ n, ∃ n', n ≤ n' → (FairLossLink.Request.Send p₂ msg) ∈ (requestsAt n' p₁))
      → (∀ n, ∃ n', n < n' → (FairLossLink.Indication.Deliver p₁ msg) ∈ (indicationsAt n' p₂))

  finiteDuplication : ∀ (p₁ p₂ : Process) (msg : 𝓂),
    (∃ n, (FairLossLink.Request.Send p₂ msg) ∉ (requestsAt n p₁))
      → (∃ n, (FairLossLink.Indication.Deliver p₁ msg) ∉ (indicationsAt n p₂))

  -- this is also bounded delivery
  noCreation : ∀ (p₁ p₂ : Process) (msg : 𝓂),
    ∃ n', (FairLossLink.Indication.Deliver p₁ msg) ∈ (indicationsAt n' p₂)
    → ∃ n, n' - DeliverTime ≤ n → n < n' → (FairLossLink.Request.Send p₂ msg) ∈ (requestsAt n p₁)

  boundedDelivery : ∀ (p₁ p₂ : Process) (msg : 𝓂),
    (∀ n, ∃ n', n ≤ n' → (FairLossLink.Request.Send p₂ msg) ∈ (requestsAt n' p₁))
      → (∀ n, ∃ n', n ≤ n' → (FairLossLink.Indication.Deliver p₁ msg) ∈ (indicationsAt n' p₂))

axiom FairLossLink.mk : (𝓂 : Type) → (t : Drace) → (requestsAt : (n : ℕ) → Process → Set (Request 𝓂)) → FairLossLink 𝓂

namespace StubbornLink
  variable (𝓂 : Type)

  inductive Request | Send (dest : Process) (msg : 𝓂)
  inductive Indication | Deliver (src : Process) (msg : 𝓂)
end StubbornLink

structure StubbornLink (𝓂 : Type) extends Component (StubbornLink.Request 𝓂) (StubbornLink.Indication 𝓂) where
  mk' ::

  fll : FairLossLink 𝓂

  stubbornDelivery : ∀ (p₁ p₂ : Process) (msg : 𝓂),
    (∀ n, ∃ n', n ≤ n' → (StubbornLink.Request.Send p₂ msg) ∈ (requestsAt n' p₁))
      → (∀ n, ∃ n', n ≤ n' → n' ≤ n + DeliverTime → (StubbornLink.Indication.Deliver p₁ msg) ∈ (indicationsAt n' p₂))

  noCreation : ∀ (p₁ p₂ : Process) (msg : 𝓂),
    (∃ n, (StubbornLink.Request.Send p₂ msg) ∉ (requestsAt n p₁))
      → (∃ n, (StubbornLink.Indication.Deliver p₁ msg) ∉ (indicationsAt n p₂))

def StubbornLink.mk (𝓂 : Type) (t : Drace) (requestsAt : (n : ℕ) → Process → Set (Request 𝓂)) : StubbornLink 𝓂 where
  t := t
  requestsAt := requestsAt
  indicationsAt := sorry
  noCrashing := sorry

  fll := FairLossLink.mk 𝓂 t (fun n p (.Send dest msg) => ∃ n' ≤ n, StubbornLink.Request.Send dest msg ∈ (requestsAt n' p))

  stubbornDelivery := sorry
  noCreation := sorry
