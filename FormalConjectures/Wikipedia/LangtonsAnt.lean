/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Langton's ant highway conjecture

Langton's ant moves on the square grid $\mathbb{Z}^2$, whose cells are black or white. On a white
cell the ant turns $90°$ clockwise, on a black cell it turns $90°$ counterclockwise. It then flips
the colour of its cell and moves forward one cell.

Started on an all-white grid, the ant eventually builds a "highway": it repeats a cycle of $104$
steps that moves it two cells diagonally.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Langton%27s_ant)
- [La86] C. G. Langton, *Studying artificial life with cellular automata*, Physica D **22**
  (1986), pp. 120-149.
- [BuTr92] L. A. Bunimovich and S. E. Troubetzkoy, *Recurrence properties of Lorentz lattice gas
  cellular automata*, J. Stat. Phys. **67** (1992), pp. 289-302.
- [GPST95] D. Gale, J. Propp, S. Sutherland and S. Troubetzkoy, *Further travels with my ant*,
  Math. Intelligencer **17** (1995), pp. 48-56.
-/

@[expose] public section

namespace LangtonsAnt

/-- A state of Langton's ant: the finite set of black cells, the cell of the ant, and the unit
vector of its heading. -/
structure State where
  black : Finset (ℤ × ℤ)
  pos : ℤ × ℤ
  dir : ℤ × ℤ

/-- The four unit vectors, which are the possible headings of the ant. -/
def headings : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 0), (0, -1)}

/-- One step of the ant. On a black cell it turns counterclockwise, on a white cell clockwise.
It then flips the colour of its cell and moves forward one cell. -/
def step (s : State) : State :=
  if s.pos ∈ s.black then
    let d := (-s.dir.2, s.dir.1)
    ⟨s.black.erase s.pos, s.pos + d, d⟩
  else
    let d := (s.dir.2, -s.dir.1)
    ⟨insert s.pos s.black, s.pos + d, d⟩

/-- The state after `t` steps from `s`. -/
def run (s : State) (t : ℕ) : State := step^[t] s

/-- After `t` steps from `s`, the ant stands on a black cell. The sequence of these colours
determines the motion of the ant up to a rotation and a translation of the grid. -/
def OnBlack (s : State) (t : ℕ) : Prop := (run s t).pos ∈ (run s t).black

instance (s : State) (t : ℕ) : Decidable (OnBlack s t) := by
  unfold OnBlack
  infer_instance

/-- The ant at the origin, heading in direction $(0, 1)$, on an all-white grid. -/
def emptyStart : State := ⟨∅, (0, 0), (0, 1)⟩

@[category test, AMS 37 68]
theorem run_emptyStart_four : (run emptyStart 4).black = {(0, 0), (1, 0), (1, -1), (0, -1)} ∧
    (run emptyStart 4).pos = (0, 0) ∧ (run emptyStart 4).dir = (0, 1) := by
  decide +kernel

@[category test, AMS 37 68]
theorem onBlack_emptyStart : (∀ t < 4, ¬ OnBlack emptyStart t) ∧ OnBlack emptyStart 4 := by
  decide +kernel

@[category test, AMS 37 68]
theorem run_emptyStart_five_pos : (run emptyStart 5).pos = (-1, 0) := by
  decide +kernel

/--
**Langton's ant highway conjecture.** From every finite initial configuration, the ant eventually
builds the same highway as from the all-white grid.

The ant on the all-white grid enters its highway after about $10^4$ steps. We state that
the colours seen by the ant from some time on agree with the colours seen by the ant on the
all-white grid from some time on. This determines the motion of the ant up to a rotation and a
translation. Bunimovich and Troubetzkoy proved that the trajectory of the ant is always unbounded
[BuTr92].
-/
@[category research open, AMS 37 68]
theorem langtons_ant_highway (black : Finset (ℤ × ℤ)) (pos dir : ℤ × ℤ) (hdir : dir ∈ headings) :
    ∃ T₀ T₁, ∀ n, OnBlack ⟨black, pos, dir⟩ (T₀ + n) ↔ OnBlack emptyStart (T₁ + n) := by
  sorry

/--
A weaker form of the highway conjecture: from every finite initial configuration, the motion of
the ant is eventually periodic with period $104$. Each period moves the ant two cells diagonally.
-/
@[category research open, AMS 37 68]
theorem langtons_ant_highway.variants.periodic (black : Finset (ℤ × ℤ)) (pos dir : ℤ × ℤ)
    (hdir : dir ∈ headings) :
    ∃ T, ∃ v ∈ ({(2, 2), (2, -2), (-2, 2), (-2, -2)} : Finset (ℤ × ℤ)), ∀ t ≥ T,
      let s : State := ⟨black, pos, dir⟩
      (run s (t + 104)).pos = (run s t).pos + v ∧ (run s (t + 104)).dir = (run s t).dir ∧
        (OnBlack s (t + 104) ↔ OnBlack s t) := by
  sorry

end LangtonsAnt
