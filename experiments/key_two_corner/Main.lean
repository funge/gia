import KeyTwoCorner
import SineProgram
import CosineProgram
open GeneralizedIntervalArithmetic.HardwareAddition

/-- Logical fallback throws. Compiled extern execution is tested below;
no theorem asserts that this IO definition equals the C implementation. -/
@[extern "gia_directed_add"]
def directedAdd (_a _b : Float) : IO (Option (Float × Float)) :=
  throw (IO.userError "hardware adapter not linked")

@[extern "gia_directed_sub"]
def directedSub (_a _b : Float) : IO (Option (Float × Float)) :=
  throw (IO.userError "hardware adapter not linked")

@[extern "gia_directed_mul"]
def directedMul (_a _b : Float) : IO (Option (Float × Float)) :=
  throw (IO.userError "hardware adapter not linked")

-- Raw corner results remain available for independent execution checks.
def cornerProducts (a b : Bounds Float) : IO (Array (Option (Float × Float))) := do
  return #[← directedMul a.lo b.lo, ← directedMul a.lo b.hi,
    ← directedMul a.hi b.lo, ← directedMul a.hi b.hi]

def chooseMin (a b : Float) : Float := if a ≤ b then a else b
def chooseMax (a b : Float) : Float := if a ≤ b then b else a

def multiply (a b : Bounds Float) : IO (Option (Bounds Float)) := do
  let ll ← directedMul a.lo b.lo
  let lh ← directedMul a.lo b.hi
  let hl ← directedMul a.hi b.lo
  let hh ← directedMul a.hi b.hi
  return GeneralizedIntervalArithmetic.HardwareMultiplication.assembleFour chooseMin chooseMax ll lh hl hh

@[extern "gia_directed_div"]
def rawDiv (_a _b : Float) : IO (Option (Float × Float)) :=
  throw (IO.userError "hardware adapter not linked")

initialize calls : IO.Ref Nat ← IO.mkRef 0

def directedDiv (a b : Float) : IO (Option (Float × Float)) := do
  calls.modify (· + 1)
  rawDiv a b

def finiteLt (a b : Float) : Bool := decide (a < b)

def divide (a b : Bounds Float) : IO (Option (Bounds Float)) := do
  unless GeneralizedIntervalArithmetic.HardwareDivision.awayZero finiteLt 0.0 b do
    return none
  let ll ← directedDiv a.lo b.lo
  let lh ← directedDiv a.lo b.hi
  let hl ← directedDiv a.hi b.lo
  let hh ← directedDiv a.hi b.hi
  return GeneralizedIntervalArithmetic.HardwareDivision.assembleGuarded
    finiteLt 0.0 chooseMin chooseMax b ll lh hl hh

@[extern "gia_directed_sqrt"]
def directedSqrt (_a : Float) : IO (Option (Float × Float)) :=
  throw (IO.userError "hardware adapter not linked")

/-- Finite partial-domain enclosure; none alone does not classify the domain. -/
def squareRoot (a : Bounds Float) : IO (Option (Bounds Float)) := do
  unless a.lo.isFinite && a.hi.isFinite do return none
  if a.hi < 0.0 || a.hi < a.lo then return none
  let lower ← directedSqrt (chooseMax a.lo 0.0)
  let upper ← directedSqrt a.hi
  return assemble lower upper

@[extern "gia_rounding_restored"]
def roundingRestored : IO Bool := throw (IO.userError "hardware adapter not linked")

def add (a b : Bounds Float) : IO (Option (Bounds Float)) := do
  let lower ← directedAdd a.lo b.lo
  let upper ← directedAdd a.hi b.hi
  return assemble lower upper

def subtract (a b : Bounds Float) : IO (Option (Bounds Float)) := do
  let lower ← directedSub a.lo b.hi
  let upper ← directedSub a.hi b.lo
  return assemble lower upper


def words (a : Bounds Float) : Bounds Nat := ⟨a.lo.toBits.toNat,a.hi.toBits.toNat⟩
def floatWord (w : Nat) : Float := Float.ofBits (UInt64.ofNat w)

def selected (selector : Bounds Nat → Bounds Nat → Option (GeneralizedIntervalArithmetic.WordTwoCorner.Requests Nat))
    (a b : Bounds Float) : IO (Option (Bounds Float)) := do
  let some p := selector (words a) (words b) | return none
  let some lo ← directedDiv (floatWord p.1.1) (floatWord p.1.2) | return none
  return assemble (some lo) (← directedDiv (floatWord p.2.1) (floatWord p.2.2))

def two := selected GeneralizedIntervalArithmetic.WordTwoCorner.requests
def fast := selected GeneralizedIntervalArithmetic.KeyTwoCorner.requests


def bits (o : Option (Bounds Float)) : String :=
  match o with
  | none => "none"
  | some v => s!"{v.lo.toBits.toNat} {v.hi.toBits.toNat}"

@[extern "gia_experiment_begin"]
def envBegin : IO Bool := throw (IO.userError "probe not linked")
@[extern "gia_experiment_end"]
def envEnd : IO Bool := throw (IO.userError "probe not linked")

def sineKernel (div : Bounds Float → Bounds Float → IO (Option (Bounds Float)))
    (i : Bounds Float) : IO (Option (Bounds Float)) :=
  GeneralizedIntervalArithmetic.HardwareSine.run
    (GeneralizedIntervalArithmetic.HardwareSine.unitGuard finiteLt 0.0 1.0)
    add subtract multiply div 0.0 ⟨6.0,6.0⟩ ⟨120.0,120.0⟩ ⟨5040.0,5040.0⟩ i

def cosineKernel (div : Bounds Float → Bounds Float → IO (Option (Bounds Float)))
    (i : Bounds Float) : IO (Option (Bounds Float)) :=
  GeneralizedIntervalArithmetic.HardwareCosine.run
    (GeneralizedIntervalArithmetic.HardwareSine.unitGuard finiteLt (-1.0) 1.0)
    add subtract multiply div chooseMin 0.0 1.0
    ⟨2.0,2.0⟩ ⟨24.0,24.0⟩ ⟨720.0,720.0⟩ ⟨40320.0,40320.0⟩ i

def workload (kind : Nat)
    (div : Bounds Float → Bounds Float → IO (Option (Bounds Float)))
    (i : Nat) : IO (Option (Bounds Float)) :=
  let x := Float.ofNat (i % 9 + 1) / 16.0
  if kind == 0 then div ⟨x,x+0.25⟩ ⟨6.0,6.0⟩
  else if kind == 1 then div ⟨-x,x+0.25⟩ ⟨-3.0,-0.5⟩
  else if kind == 2 then sineKernel div ⟨x,x+0.125⟩
  else if kind == 3 then cosineKernel div ⟨-x,x+0.125⟩
  else div ⟨-x,x+0.25⟩ ⟨0.5,3.0⟩

def sample (kind : Nat) (mode : Nat) (repeats : Nat) : IO Unit := do
  let div := if mode == 0 then divide else if mode == 1 then two else fast
  calls.set 0
  let mut good := 0
  let mut digest : UInt64 := 0
  let start ← IO.monoNanosNow
  for i in [:repeats] do
    let result ← workload kind div i
    if let some o := result then
      good := good+1
      digest := digest ^^^ o.lo.toBits ^^^ o.hi.toBits
  let finish ← IO.monoNanosNow
  let count ← calls.get
  IO.println s!"BENCH {kind} {mode} {repeats} {good} {count} {finish-start} {digest}"

def kernels : IO Unit := do
  for kind in [:5] do
    for i in [:9] do
      let old ← workload kind divide i
      let reference ← workload kind two i
      let fresh ← workload kind fast i
      IO.println s!"KERNEL {kind} {i} {bits fresh} | {bits reference} | {bits old}"

def selectorSample (mode repeats : Nat) : IO Unit := do
  let select := if mode == 1 then GeneralizedIntervalArithmetic.WordTwoCorner.requests
    else GeneralizedIntervalArithmetic.KeyTwoCorner.requests
  let mut good := 0
  let mut digest : Nat := 0
  let start ← IO.monoNanosNow
  for i in [:repeats] do
    let x := Float.ofNat (i % 9 + 1) / 16.0
    let input := words ⟨-x,x+0.25⟩
    let denom := if i % 4 == 0 then words ⟨-0.0,2.0⟩ else words ⟨-3.0,-0.5⟩
    if let some p := select input denom then
      good := good+1
      digest := digest ^^^ p.1.1 ^^^ p.1.2 ^^^ p.2.1 ^^^ p.2.2
  let finish ← IO.monoNanosNow
  IO.println s!"SELECT {mode} {repeats} {good} {finish-start} {digest}"

def benchmark : IO Unit := do
  for kind in [:5] do
    for mode in [:3] do sample kind mode 200
    for rep in [:9] do
      for step in [:3] do sample kind ((rep+step)%3) 2000
  selectorSample 1 200
  selectorSample 2 200
  for rep in [:10] do
    selectorSample (1+rep%2) 2000
    selectorSample (2-rep%2) 2000

def planBits (p : Option (GeneralizedIntervalArithmetic.WordTwoCorner.Requests Nat)) : String :=
  match p with
  | none => "none"
  | some p => s!"{p.1.1} {p.1.2} {p.2.1} {p.2.2}"

def main (args : List String) : IO Unit := do
  unless ← roundingRestored do throw (IO.userError "core restoration failed")
  if args == ["kernels"] then
    kernels
    return
  if args == ["bench"] then
    benchmark
    return
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let ws := (line.trim.splitOn " ").filter (· != "")
    let ns := ws.map String.toNat!
    match ns with
    | [a,b,c,d] =>
      let i := Bounds.mk (floatWord a) (floatWord b)
      let j := Bounds.mk (floatWord c) (floatWord d)
      -- Preserve and report bridge observations, including NaN canonicalization.
      let actual := [i.lo.toBits.toNat,i.hi.toBits.toNat,j.lo.toBits.toNat,j.hi.toBits.toNat]
      let bridge := String.intercalate " " (actual.map toString)
      let referenceRequests := GeneralizedIntervalArithmetic.WordTwoCorner.requests (words i) (words j)
      let keyRequests := GeneralizedIntervalArithmetic.KeyTwoCorner.requests (words i) (words j)
      unless referenceRequests == keyRequests do throw (IO.userError "native request mismatch")
      calls.set 0
      unless ← envBegin do throw (IO.userError "environment setup")
      let r ← two i j
      unless ← envEnd do throw (IO.userError "two environment changed")
      let n ← calls.get
      calls.set 0
      unless ← envBegin do throw (IO.userError "environment setup")
      let old ← divide i j
      let oldEnv ← envEnd
      let m ← calls.get
      calls.set 0
      unless ← envBegin do throw (IO.userError "environment setup")
      let optimized ← fast i j
      unless ← envEnd do throw (IO.userError "key environment changed")
      let k ← calls.get
      stdout.putStrLn s!"{bits r} | {n} | {bits old} | {m} | {oldEnv} | {bridge} | {bits optimized} | {k} | {planBits keyRequests}"
    | _ => throw (IO.userError "expected four raw words")
  let _ := args
