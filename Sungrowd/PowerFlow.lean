import Std.Tactic.BVDecide

-- set_option profiler true
-- set_option profiler.threshold 10

namespace Sungrowd

/-- One bit of register 13000, "power flow status" (older docs: "running state"). The bits and
labels are the template binary sensors in `reference/modbus_sungrow.yaml`; 0x40 is not defined
there. Unlike `RunningState`, several of these can be set at once. -/
inductive PowerFlow
  | pvGenerating
  | batteryCharging
  | batteryDischarging
  | positiveLoad
  | exporting
  | importing
  | negativeLoad
  deriving DecidableEq, Repr

def PowerFlow.all : List PowerFlow :=
  [.pvGenerating, .batteryCharging, .batteryDischarging, .positiveLoad, .exporting, .importing,
   .negativeLoad]

def PowerFlow.bit : PowerFlow → UInt16
  | .pvGenerating       => 0x01
  | .batteryCharging    => 0x02
  | .batteryDischarging => 0x04
  | .positiveLoad       => 0x08
  | .exporting          => 0x10
  | .importing          => 0x20
  | .negativeLoad       => 0x80

/-- The YAML's binary sensor names, verbatim. -/
def PowerFlow.label : PowerFlow → String
  | .pvGenerating       => "PV generating"
  | .batteryCharging    => "Battery charging"
  | .batteryDischarging => "Battery discharging"
  | .positiveLoad       => "Positive Load Power"
  | .exporting          => "Exporting Power"
  | .importing          => "Importing Power"
  | .negativeLoad       => "Negative Load Power"

/-- Every bit that has a name. -/
def PowerFlow.knownMask : UInt16 := PowerFlow.all.foldl (· ||| ·.bit) 0

/-- The flags set in `v`, in bit order. Bits outside `knownMask` are dropped; see `unknownBits`. -/
def PowerFlow.flags (v : UInt16) : List PowerFlow :=
  PowerFlow.all.filter fun f => v &&& f.bit != 0

def PowerFlow.unknownBits (v : UInt16) : UInt16 := v &&& ~~~PowerFlow.knownMask

def PowerFlow.toRaw (fs : List PowerFlow) : UInt16 := fs.foldl (· ||| ·.bit) 0

/-
Concise version: unfold everything, case split on all 7 `if`s inside `List.filter`
(2^7 = 128 goals, each with a concrete list of flags), and hand each to the SAT solver.
Correct, but ~10 s to check because of the 128 `bv_decide` calls.

theorem PowerFlow.toRaw_flags (v : UInt16) : toRaw (flags v) ||| unknownBits v = v := by
  simp only [toRaw, flags, unknownBits, knownMask, all, List.filter]
  split <;> split <;> split <;> split <;> split <;> split <;> split <;>
    simp only [List.foldl, bit, bne_iff_ne, ne_eq, bne_eq_false_iff_eq] at * <;> bv_decide
-/

/-- Filtering a list and then OR-ing the survivors' bits is the same as OR-ing in every
element's bit conditionally. This is what lets the main proof avoid case splits: the list
structure disappears and only bit-vector `if`s remain, which `bv_decide` handles natively. -/
theorem PowerFlow.foldl_filter (p : PowerFlow → Bool) (acc : UInt16) (l : List PowerFlow) :
    (l.filter p).foldl (· ||| ·.bit) acc
      = l.foldl (fun acc f => acc ||| if p f then f.bit else 0) acc := by
  -- `generalizing acc`: the accumulator changes at each step, so the induction hypothesis
  -- must hold for every `acc`, not just the one we started with.
  induction l generalizing acc with
  | nil =>
    -- Both sides fold over `[]`, so both are just `acc`.
    rfl
  | cons f fs ih =>
    -- ih : ∀ acc, foldl _ acc (filter p fs) = foldl _ acc fs
    -- ⊢ foldl _ acc (filter p (f :: fs)) = foldl _ acc (f :: fs)
    by_cases hp : p f
    · -- `f` survives the filter: the left side folds `acc ||| f.bit` over `filter p fs`,
      -- the right side folds `acc ||| (if true then f.bit else 0)` over `fs`. Same thing,
      -- by `ih` at the new accumulator.
      simp only [List.filter, hp, List.foldl, ih, ite_true]
    · -- `f` is dropped: the left side keeps `acc`, the right side ORs in `0`.
      have hz : acc ||| 0 = acc := UInt16.or_zero
      simp only [List.filter, hp, List.foldl, ih, Bool.false_eq_true, ite_false, hz]

/-- Decoding loses nothing: the named flags plus the unknown bits rebuild the register. -/
theorem PowerFlow.toRaw_flags (v : UInt16) : toRaw (flags v) ||| unknownBits v = v := by
  -- ⊢ toRaw (flags v) ||| unknownBits v = v
  rw [toRaw, flags, foldl_filter]
  -- ⊢ List.foldl (fun acc f => acc ||| if (v &&& f.bit != 0) = true then f.bit else 0) 0 all
  --     ||| unknownBits v = v
  --
  -- Now unfold the concrete list `all` (seven `foldl` steps), each flag's `bit`, and the mask,
  -- and turn the Boolean test `!= 0` into the proposition `¬ … = 0` that `bv_decide` understands.
  simp only [unknownBits, knownMask, all, List.foldl, bit, bne_iff_ne, ne_eq]
  -- ⊢ (0 ||| if ¬v &&& 1 = 0 then 1 else 0) ||| … ||| (if ¬v &&& 128 = 0 then 128 else 0)
  --     ||| v &&& ~~~(0 ||| 1 ||| 2 ||| 4 ||| 8 ||| 16 ||| 32 ||| 128) = v
  --
  -- A statement about one 16-bit vector `v`, with no lists left: one SAT query.
  bv_decide

/-- e.g. `"21 (PV generating, Battery discharging, Exporting Power)"`. Unknown bits are shown
in hex rather than dropped. -/
def PowerFlow.labelRaw (v : UInt16) : String :=
  let names := (PowerFlow.flags v).map (·.label)
  let names := if unknownBits v == 0 then names
    else names ++ [s!"unknown bits 0x{(unknownBits v).toBitVec.toHex}"]
  s!"{v} ({", ".intercalate names})"

#guard PowerFlow.knownMask == 0xBF
-- Seen on the real inverter: forced charge from the grid, then self-consumption, then evening.
#guard PowerFlow.flags 35 == [.pvGenerating, .batteryCharging, .importing]
#guard PowerFlow.flags 3  == [.pvGenerating, .batteryCharging]
#guard PowerFlow.flags 21 == [.pvGenerating, .batteryDischarging, .exporting]
#guard PowerFlow.labelRaw 0x41 == "65 (PV generating, unknown bits 0x0040)"

end Sungrowd


