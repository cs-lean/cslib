/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Batteries.Util.ProofWanted
import Cslib.Logic.LinearLogic.CLL.Basic

namespace CLL

/-- A proof is cut-free if it does not contain any applications of rule cut. -/
def Proof.cutFree (p : @Proof Atom Γ) : Prop :=
  match p with
  | ax => True
  | cut _ _ => False
  | exchange _ p => p.cutFree
  | one => True
  | bot p => p.cutFree
  | parr p => p.cutFree
  | tensor p q => p.cutFree ∧ q.cutFree
  | oplus₁ p => p.cutFree
  | oplus₂ p => p.cutFree
  | Proof.with p q => p.cutFree ∧ q.cutFree
  | top => True
  | quest p => p.cutFree
  | weaken p => p.cutFree
  | contract p => p.cutFree
  | bang _ p => p.cutFree

/-- Cut elimination: for any sequent Γ, if there is a proof of Γ, then there exists a cut-free
proof of Γ. -/
proof_wanted Proof.cut_elim (p : @Proof Atom Γ) : ∃ q : @Proof Atom Γ, q.cutFree

end CLL
