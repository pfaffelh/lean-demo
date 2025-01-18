import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Instances.Nat
import Mathlib.Order.Filter.AtTopBot

open Filter

example : NeBot (atTop : Filter ℕ) := by
  exact atTop_neBot

example (x : ℕ → ℝ) (y z : ℝ) (hy: Tendsto x atTop (nhds y)) (hz : Tendsto x atTop (nhds z)) : y = z := by
   refine tendsto_nhds_unique hy hz

example {ι : Type} (x : ι → ℝ) (y z : ℝ) (l : Filter ι) (hl: l.NeBot) (hy: Tendsto x l (nhds y)) (hz : Tendsto x l (nhds z)) : y = z := by
  refine tendsto_nhds_unique hy hz
