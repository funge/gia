import AccuracySearchExample

open GeneralizedIntervalArithmetic GeneralizedIntervalArithmetic.ExpressionStreams
open GeneralizedIntervalArithmetic.AccuracySearchExample

def main : IO Unit := do
  let states := (List.range 4).map fun n =>
    (eval exactBackend (input n) (.point 0) nested).isNone
  unless states == [true,true,false,false] do throw (IO.userError "unexpected division trace")
  let n := selected
  unless n == 2 do throw (IO.userError s!"unexpected search index {n}")
  match eval exactBackend (input n) (.point 0) nested with
  | none => throw (IO.userError "search returned failure")
  | some I =>
    unless I.lo == 2 && I.hi == 2 && precisionTest (1/100) (some I) do
      throw (IO.userError "unexpected output bounds")
  IO.println s!"compiled search: rejected stages 0,1; selected {n}; bounds [2,2]; tolerance 1/100"
