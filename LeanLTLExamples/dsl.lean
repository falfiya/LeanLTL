import LeanLTL
import Mathlib
import Mathlib.Data.Set.Basic

namespace LeanLTL.Examples.DistributedSystems

example (raining wet : Prop) : raining → wet → raining := by
  intros r w
  exact r

structure Process where
  id : ℕ

axiom P : Set Process

namespace CrashFault.Sync
-- Crash-fault, Synchronous Protocols

open LeanLTL
open LeanLTL.Notation

axiom MaxDeliverTime : ℕ

instance {α : Type} : Membership α (Option $ Set α) where
  mem
  | .some s, a => a ∈ s
  | _, _ => False

namespace FairLossLink
  variable {𝓂 : Type}

  inductive Request | Send (dest : Process) (msg : 𝓂)
  inductive Indication | Deliver (src : Process) (msg : 𝓂)

  structure ε where
    requests : Set $ @Request 𝓂
    indications : Set $ @Indication 𝓂

  -- Events at a point in time for some process
  def σ := Process → Option (@ε 𝓂)
  instance : Inhabited $ @σ 𝓂 where
    default _ := .none

  -- LLTL Version
  def crashed (s : @σ 𝓂) (p : Process) := (s p).isNone
  def requests (s : @σ 𝓂) (p : Process) := (s p).map ε.requests
  def indications (s : @σ 𝓂) (p : Process) := (s p).map ε.indications

  -- Tried to write the most simple one using LLTL and failed.
  -- def fairLoss' : @ts 𝓂 := LLTL[∀ p₁ p₂ msg,
  --   (𝐆 (𝐅 ((Request.Send p₂ msg) ∈ ((← requests) p₁))))
  --     → (𝐆 (𝐅 (crashed ∨ ((Indication.Deliver p₁ msg) ∈ (← indications p₂)))))
  -- ]

  -- Handmade Version
  def Trace' := Trace $ @σ 𝓂
  def TraceSet' := TraceSet $ @σ 𝓂
  def crashedAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).isNone
  def requestsAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).map ε.requests
  def indicationsAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).map ε.indications

  def fairLoss : @TraceSet' 𝓂 where
    sat t := ∀ (p₁ p₂ : Process) (msg : 𝓂),
      (∀ n, ∃ sendTime, n ≤ sendTime ∧ (.Send p₂ msg) ∈ (requestsAt t sendTime p₁))
      → (∀ n, ∃ deliverTime, n < deliverTime ∧ (
          (crashedAt t deliverTime p₂) ∨ (.Deliver p₁ msg) ∈ (indicationsAt t deliverTime p₂)))

  def finiteDuplication : @TraceSet' 𝓂 where
    sat t := ∀ (p₁ p₂ : Process) (msg : 𝓂),
      (∃ noMoreSending, (.Send p₂ msg) ∉ (requestsAt t noMoreSending p₁))
        → (∃ noMoreDelivering, (.Deliver p₁ msg) ∉ (indicationsAt t noMoreDelivering p₂))

  def noCreation : @TraceSet' 𝓂 where
    sat t := ∀ (p₁ p₂ : Process) (msg : 𝓂) deliverTime,
      ((.Deliver p₁ msg) ∈ (indicationsAt t deliverTime p₂))
      → ∃ sendTime, sendTime < deliverTime ∧ deliverTime ≤ sendTime + MaxDeliverTime
          ∧ (.Send p₂ msg) ∈ (requestsAt t sendTime p₁)

end FairLossLink
open FairLossLink in
def FairLossLink {𝓂 : Type} : @TraceSet' 𝓂 := LLTL[fairLoss ∧ finiteDuplication ∧ noCreation]

namespace StubbornLink
  variable {𝓂 : Type}

  inductive Request | Send (dest : Process) (msg : 𝓂)
  inductive Indication | Deliver (src : Process) (msg : 𝓂)

  structure ε where
    requests : Set $ @Request 𝓂
    indications : Set $ @Indication 𝓂

  def σ := Process → Option (@ε 𝓂)
  instance : Inhabited $ @σ 𝓂 where
    default _ := .none

    def T := Trace $ @σ 𝓂
    def TS := TraceSet $ @σ 𝓂
    def crashedAt (t : @T 𝓂) n (p : Process) := (t.toFun! n p).isNone
    def requestsAt (t : @T 𝓂) n (p : Process) := (t.toFun! n p).map ε.requests
    def indicationsAt (t : @T 𝓂) n (p : Process) := (t.toFun! n p).map ε.indications

    -- LLTL Version
    def crashed (s : @σ 𝓂) (p : Process) := (s p).isNone
    def requests (s : @σ 𝓂) (p : Process) := (s p).map ε.requests
    def indications (s : @σ 𝓂) (p : Process) := (s p).map ε.indications
end StubbornLink

open StubbornLink in
def StubbornLink {𝓂 : Type} : @TS 𝓂 where
  sat t :=
    -- There is a fair loss link that runs in lockstep with the stubborn link.
    ∃ fll_t : @FairLossLink.Trace' 𝓂, (fll_t ⊨ FairLossLink)
    -- And it runs for as long as the stubborn link
    ∧ fll_t.length = t.length
    -- And a process crashes on both at the same time
    ∧ (∀ n p, crashedAt t n p ↔ FairLossLink.crashedAt fll_t n p)
    -- Here are the requests made to it.
    ∧ (∀ n p₁ p₂ msg,
        ∃ n' ≤ n, ((.Send p₂ msg) ∈ requestsAt t n p₁)
        → ((.Send p₂ msg) ∈ FairLossLink.requestsAt fll_t n p₁))
    -- Now that we have our fair loss link, and it's up and running, we need to filter our stubborn
    -- link indications.
    --
    -- The stubborn link delivers whenever the fair loss link delivers.
    ∧ (∀ n p₁ p₂ msg,
        (.Deliver p₁ msg) ∈ FairLossLink.indicationsAt fll_t n p₂
        → ((.Deliver p₁ msg) ∈ indicationsAt t n p₂))

namespace StubbornLink
  variable {𝓂 : Type}
  theorem stubbornDelivery (p₁ p₂ : Process) (msg : 𝓂) :
    ⊨ⁱ LLTL[StubbornLink → 𝐆 (𝐅 ((.Send p₂ msg) ∈ ((← requests) p₁)) → 𝐆 𝐅 (((← crashed) p₂) = true ∨ (.Deliver p₁ msg) ∈ ((← indications) p₂)))] := by
      simp +contextual [push_ltl]
      rintro t t_inf ⟨fll_t, ⟨fairloss, fll_t_len, crashes, subreq, delivery⟩⟩ x y req z
      unfold FairLossLink at fairloss
      simp +contextual [push_ltl] at fairloss
      replace fairloss := fairloss.1
      unfold FairLossLink.fairLoss at fairloss
      simp at fairloss
      specialize fairloss p₁ p₂ msg
      have infiniteSend : ∀ (n : ℕ), ∃ sendTime, n ≤ sendTime ∧ FairLossLink.Request.Send p₂ msg ∈ FairLossLink.requestsAt fll_t sendTime p₁ := by
        sorry
      specialize fairloss infiniteSend (z + x)
      obtain ⟨deliverTime, ⟨deliverTimeLowerBound, crashedOrDelivered⟩⟩ := fairloss
      exists (deliverTime - (z + x))
      rw [@Nat.sub_add_cancel deliverTime (z + x) deliverTimeLowerBound.le]
      match crashedOrDelivered with
      | .inl crashed =>
        left
        replace crashes := (crashes deliverTime p₂).mpr
        exact crashes crashed
      | .inr delivered =>
        right
        replace delivery := delivery deliverTime p₁ p₂ msg
        unfold indicationsAt at delivery
        unfold indications
        exact delivery delivered
