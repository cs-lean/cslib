/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logic.LinearLogic.CLL.Basic
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.AddSub

universe u

variable {Atom : Type u}

namespace CLL

/-- A sequent in CLL, as a multiset. -/
abbrev MSequent (Atom) := Multiset (Proposition Atom)

/-- Checks that all propositions in `Γ` are question marks. -/
-- TODO: This and Sequent.AllQuest can probably be unified, we just need Mem.
def MSequent.AllQuest (Γ : MSequent Atom) :=
  ∀ a ∈ Γ, ∃ b, a = Proposition.quest b

open Proposition in
/-- CLL sequent calculus based on `Multiset`. -/
inductive MProof : MSequent Atom → Prop where
  | ax : MProof {a, a.dual}
  | cut : MProof (a ::ₘ Γ) → MProof (a.dual ::ₘ Δ) → MProof (Γ + Δ)
  | one : MProof {one}
  | bot : MProof Γ → MProof (⊥ ::ₘ Γ)
  | parr : MProof (a ::ₘ b ::ₘ Γ) → MProof ((a ⅋ b) ::ₘ Γ)
  | tensor : MProof (a ::ₘ Γ) → MProof (b ::ₘ Δ) → MProof ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : MProof (a ::ₘ Γ) → MProof ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : MProof (b ::ₘ Γ) → MProof ((a ⊕ b) ::ₘ Γ)
  | with : MProof (a ::ₘ Γ) → MProof (b ::ₘ Γ) → MProof ((a & b) ::ₘ Γ)
  | top : MProof (top ::ₘ Γ)
  | quest : MProof (a ::ₘ Γ) → MProof (ʔa ::ₘ Γ)
  | weaken : MProof Γ → MProof (ʔa ::ₘ Γ)
  | contract : MProof (ʔa ::ₘ ʔa ::ₘ Γ) → MProof (ʔa ::ₘ Γ)
  | bang {Γ : MSequent Atom} {a} : Γ.AllQuest → MProof (a ::ₘ Γ) → MProof ((!a) ::ₘ Γ)

/- Characterisation of `Proof` and `MProof`.
theorem mproof_iff_proof {Γ : Sequent Atom} : Proof Γ ↔ MProof (Multiset.ofList Γ) := by
  apply Iff.intro
  case mp =>
    intro p
    induction p
    case ax =>
      constructor
    case cut a Γ Δ p q ihp ihq =>
      rw [← Multiset.coe_add]
      rw [← Multiset.cons_coe] at ihp ihq
      apply MProof.cut ihp ihq
    case exchange Γ Δ hperm p ihp =>
      rw [Multiset.coe_eq_coe.2 hperm] at ihp
      exact ihp
-/

end CLL
