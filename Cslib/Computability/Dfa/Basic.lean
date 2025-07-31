/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.Lts.Basic

structure Dfa (State : Type _) (Label : Type _) where
  -- The transition system of the automaton
  lts : Lts State Label
  -- Start state
  start : State
  -- Accept states
  accept : Finset State
  -- The automaton is finite-state
  finite_state : lts.FiniteState
  -- The automaton is deterministic
  deterministic : lts.Deterministic
