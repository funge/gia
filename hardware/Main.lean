import CosineProgram
import QuadrantProgram
import SineReductionProgram
import HardwareBounds
import SineProgram

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
def directedDiv (_a _b : Float) : IO (Option (Float × Float)) :=
  throw (IO.userError "hardware adapter not linked")

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

/-- Restricted-domain Taylor enclosure, using only directed arithmetic. -/
def sine (a : Bounds Float) : IO (Option (Bounds Float)) := do
  unless a.lo.isFinite && a.hi.isFinite do return none
  GeneralizedIntervalArithmetic.HardwareSine.run
    (GeneralizedIntervalArithmetic.HardwareSine.unitGuard finiteLt 0.0 1.0)
    add subtract multiply divide 0.0 ⟨6.0, 6.0⟩ ⟨120.0, 120.0⟩ ⟨5040.0, 5040.0⟩ a

/-- Monotone endpoint enclosure on [-1,1], with subtraction-based reflection. -/
def sineEndpoints (a : Bounds Float) : IO (Option (Bounds Float)) := do
  unless a.lo.isFinite && a.hi.isFinite do return none
  GeneralizedIntervalArithmetic.HardwareSine.endpoints
    (GeneralizedIntervalArithmetic.HardwareSine.unitGuard finiteLt (-1.0) 1.0)
    (GeneralizedIntervalArithmetic.HardwareSine.signedPoint finiteLt 0.0 subtract sine) a

/-- Adjacent binary64 endpoints whose exact dyadic values bracket pi in Lean. -/
def piBounds : Bounds Float :=
  ⟨Float.ofBits 0x400921fb54442d18, Float.ofBits 0x400921fb54442d19⟩

/-- Try certified whole-period shifts; no guessed quotient is treated as exact. -/
def sineReduced (a : Bounds Float) : IO (Option (Bounds Float)) := do
  unless a.lo.isFinite && a.hi.isFinite do return none
  if finiteLt a.hi a.lo then return none
  GeneralizedIntervalArithmetic.HardwareSine.searchPeriods multiply subtract sineEndpoints
    piBounds a (GeneralizedIntervalArithmetic.HardwareSine.periodCandidates 0.0 2.0 (-2.0) 4.0 (-4.0))

def cosine (a : Bounds Float) : IO (Option (Bounds Float)) := do
  unless a.lo.isFinite && a.hi.isFinite do return none
  GeneralizedIntervalArithmetic.HardwareCosine.run
    (GeneralizedIntervalArithmetic.HardwareSine.unitGuard finiteLt (-1.0) 1.0)
    add subtract multiply divide chooseMin 0.0 1.0
    ⟨2.0,2.0⟩ ⟨24.0,24.0⟩ ⟨720.0,720.0⟩ ⟨40320.0,40320.0⟩ a

def markFloat : GeneralizedIntervalArithmetic.HardwareQuadrants.Mark → Float
  | .neg4 => -4.0 | .neg375 => -3.75 | .neg225 => -2.25 | .neg075 => -0.75
  | .pos075 => 0.75 | .pos225 => 2.25 | .pos375 => 3.75 | .pos4 => 4.0
  | .neg15 => -1.5 | .neg1 => -1.0 | .neg05 => -0.5 | .zero => 0.0
  | .pos05 => 0.5 | .pos1 => 1.0 | .pos15 => 1.5

def sineQuadrants (a : Bounds Float) : IO (Option (Bounds Float)) := do
  unless a.lo.isFinite && a.hi.isFinite do return none
  GeneralizedIntervalArithmetic.HardwareQuadrants.run
    (GeneralizedIntervalArithmetic.HardwareSine.unitGuard finiteLt (-4.0) 4.0)
    finiteLt chooseMin chooseMax
    (GeneralizedIntervalArithmetic.HardwareQuadrants.evaluate
      multiply subtract sineEndpoints cosine 0.0 piBounds)
    (GeneralizedIntervalArithmetic.HardwareQuadrants.table markFloat) a

def sineGlobal (a : Bounds Float) : IO (Option (Bounds Float)) :=
  GeneralizedIntervalArithmetic.HardwareSine.globalFallback
    (fun I => I.lo.isFinite && I.hi.isFinite && !(finiteLt I.hi I.lo))
    (fun I => GeneralizedIntervalArithmetic.HardwareSine.searchPeriods multiply subtract
      sineQuadrants piBounds I
      (GeneralizedIntervalArithmetic.HardwareSine.periodCandidates 0.0 2.0 (-2.0) 4.0 (-4.0)))
    (-1.0) 1.0 a

def checkWith (op : Bounds Float → Bounds Float → IO (Option (Bounds Float))) (name : String) (a b : Bounds Float) (expected : Option (UInt64 × UInt64)) : IO Unit := do
  let result ← op a b
  let bits := result.map fun r => (r.lo.toBits, r.hi.toBits)
  if bits != expected then throw (IO.userError s!"{name}: unexpected bits {repr bits}")
  IO.println s!"PASS {name}: {repr bits}"

def check := checkWith add

def checkCosineQuadrants (one : Bounds Float) (tiny nan inf nextOne : Float) : IO Unit := do
  let cosCheck := checkWith (fun a _ => cosine a)
  cosCheck "cosine at zero" ⟨0.0,0.0⟩ one (some (0x3ff0000000000000,0x3ff0000000000000))
  cosCheck "cosine outside domain unknown" ⟨-1.0,nextOne⟩ one none
  cosCheck "cosine reversed unknown" ⟨1.0,-1.0⟩ one none
  cosCheck "cosine NaN unknown" ⟨nan,0.0⟩ one none
  let mut cosInputs : Array (Bounds Float) := #[⟨-1.0,1.0⟩,⟨-tiny,tiny⟩,⟨-0.5,0.75⟩]
  for k in [:33] do
    let x := k.toFloat / 16.0 - 1.0
    cosInputs := cosInputs.push ⟨x,x⟩
    if k < 32 then cosInputs := cosInputs.push ⟨x,x+0.0625⟩
  for a in cosInputs do
    let some r ← cosine a | throw (IO.userError "supported cosine failed")
    IO.println s!"COSINE {a.lo.toBits} {a.hi.toBits} {r.lo.toBits} {r.hi.toBits}"
  let qCheck := checkWith (fun a _ => sineQuadrants a)
  qCheck "quadrants outside domain unknown" ⟨-4.0,4.5⟩ one none
  qCheck "quadrants reversed unknown" ⟨4.0,-4.0⟩ one none
  qCheck "quadrants infinity unknown" ⟨-inf,inf⟩ one none
  qCheck "quadrants NaN unknown" ⟨nan,0.0⟩ one none
  let mut qInputs : Array (Bounds Float) := #[⟨-4.0,4.0⟩,⟨1.5,1.75⟩,⟨-1.75,-1.5⟩,
    ⟨-tiny,tiny⟩,⟨0.0,4.0⟩,⟨-4.0,0.0⟩]
  for k in [:65] do
    let x := k.toFloat / 8.0 - 4.0
    qInputs := qInputs.push ⟨x,x⟩
    if k < 64 then qInputs := qInputs.push ⟨x,x+0.125⟩
  for boundary in #[-3.75,-2.25,-0.75,0.75,2.25,3.75] do
    qInputs := qInputs.push ⟨boundary-0.0625,boundary+0.0625⟩
  for bits in #[0x3fe8000000000000,0x4002000000000000,0x400e000000000000] do
    let l := Float.ofBits (bits-1)
    let u := Float.ofBits (bits+1)
    qInputs := qInputs.push ⟨l,u⟩
    qInputs := qInputs.push ⟨-u,-l⟩
  qInputs := qInputs.push ⟨piBounds.lo/2.0,piBounds.hi/2.0⟩
  qInputs := qInputs.push ⟨-piBounds.hi/2.0,-piBounds.lo/2.0⟩
  for a in qInputs do
    let some r ← sineQuadrants a | throw (IO.userError "supported quadrant cover failed")
    IO.println s!"QUADRANTS {a.lo.toBits} {a.hi.toBits} {r.lo.toBits} {r.hi.toBits}"
  let failedCos ← GeneralizedIntervalArithmetic.HardwareCosine.run
    (fun _ => true) add subtract multiply (fun _ _ => pure none) chooseMin 0.0 1.0
    one one one one one
  unless failedCos.isNone do throw (IO.userError "cosine failure accepted")
  let failedCover ← GeneralizedIntervalArithmetic.HardwareQuadrants.run
    (fun _ => true) finiteLt chooseMin chooseMax (fun _ _ => pure none)
    (GeneralizedIntervalArithmetic.HardwareQuadrants.table markFloat) one
  unless failedCover.isNone do throw (IO.userError "cover lost a failed cell")
  let failedLater ← GeneralizedIntervalArithmetic.HardwareQuadrants.run
    (fun _ => true) finiteLt chooseMin chooseMax
    (fun c _ => if c.coefficient == 0.0 then pure (some one) else pure none)
    (GeneralizedIntervalArithmetic.HardwareQuadrants.table markFloat) ⟨0.0,4.0⟩
  unless failedLater.isNone do throw (IO.userError "later failed cell was discarded")
  IO.println "PASS cosine and quadrant failure controls"

def checkGlobal (one : Bounds Float) (nan inf : Float) : IO Unit := do
  let test := checkWith (fun a _ => sineGlobal a)
  test "global sine NaN unknown" ⟨nan,0.0⟩ one none
  test "global sine infinity unknown" ⟨-inf,inf⟩ one none
  test "global sine reversed unknown" ⟨2.0,1.0⟩ one none
  let huge := Float.ofBits 0x7fefffffffffffff
  let mut inputs : Array (Bounds Float) := #[⟨-huge,huge⟩,⟨huge,huge⟩,
    ⟨-huge,-huge⟩,⟨100.0,100.0⟩,⟨-20.0,20.0⟩,⟨0.0,7.0⟩,
    ⟨7.5,8.0⟩,⟨-8.0,-7.5⟩,⟨13.5,14.0⟩,⟨-14.0,-13.5⟩]
  for k in [:129] do
    let x := k.toFloat / 4.0 - 16.0
    inputs := inputs.push ⟨x,x⟩
    if k < 128 then inputs := inputs.push ⟨x,x+0.25⟩
  for I in inputs do
    let some O ← sineGlobal I | throw (IO.userError "finite global sine failed")
    IO.println s!"GLOBAL {I.lo.toBits} {I.hi.toBits} {O.lo.toBits} {O.hi.toBits}"
  let failed ← GeneralizedIntervalArithmetic.HardwareSine.globalFallback
    (fun _ => true) (fun _ => pure none) (-1.0) 1.0 one
  unless failed.map (fun O => (O.lo.toBits,O.hi.toBits)) ==
      some (0xbff0000000000000,0x3ff0000000000000) do
    throw (IO.userError "failed refinement did not return certified global bound")
  IO.println "PASS global fallback and unsupported controls"

def main : IO Unit := do
  let one : Bounds Float := ⟨1.0, 1.0⟩
  -- 2^-53: halfway between 1 and its next binary64 neighbor when added to 1.
  let half := Float.ofBits 0x3ca0000000000000
  check "halfway positive" one ⟨half, half⟩ (some (0x3ff0000000000000, 0x3ff0000000000001))
  check "halfway negative" ⟨-1.0, -1.0⟩ ⟨-half, -half⟩ (some (0xbff0000000000001, 0xbff0000000000000))
  check "interval corners" ⟨1.0, 2.0⟩ ⟨3.0, 4.0⟩ (some (0x4010000000000000, 0x4018000000000000))
  let tiny := Float.ofBits 1
  check "subnormal addition" ⟨tiny, tiny⟩ ⟨tiny, tiny⟩ (some (2, 2))
  check "signed cancellation" one ⟨-1.0, -1.0⟩ (some (0x8000000000000000, 0))
  let largest := Float.ofBits 0x7fefffffffffffff
  check "overflow unknown" ⟨largest, largest⟩ ⟨largest, largest⟩ none
  let inf := Float.ofBits 0x7ff0000000000000
  check "infinity unknown" ⟨inf, inf⟩ one none
  let nan := Float.ofBits 0x7ff8000000000000
  check "NaN unknown" ⟨nan, nan⟩ one none
  let sub := checkWith subtract
  sub "sub crossed corners" ⟨1.0, 2.0⟩ ⟨3.0, 4.0⟩ (some (0xc008000000000000, 0xbff0000000000000))
  sub "sub halfway positive" one ⟨-half, -half⟩ (some (0x3ff0000000000000, 0x3ff0000000000001))
  sub "sub halfway negative" ⟨-1.0, -1.0⟩ ⟨half, half⟩ (some (0xbff0000000000001, 0xbff0000000000000))
  let quarter := Float.ofBits 0x3c90000000000000
  sub "sub midpoint below one" one ⟨quarter, quarter⟩ (some (0x3fefffffffffffff, 0x3ff0000000000000))
  let twiceTiny := Float.ofBits 2
  sub "sub subnormal" ⟨twiceTiny, twiceTiny⟩ ⟨tiny, tiny⟩ (some (1, 1))
  sub "sub cancellation" one one (some (0x8000000000000000, 0))
  sub "sub overflow unknown" ⟨largest, largest⟩ ⟨-largest, -largest⟩ none
  sub "sub infinity unknown" one ⟨inf, inf⟩ none
  sub "sub NaN unknown" one ⟨nan, nan⟩ none
  let products ← cornerProducts ⟨-2.0, 3.0⟩ ⟨-4.0, 5.0⟩
  let productBits := products.map fun p => p.map fun q => (q.1.toBits, q.2.toBits)
  let expected : Array (Option (UInt64 × UInt64)) := #[
    some (0x4020000000000000, 0x4020000000000000),
    some (0xc024000000000000, 0xc024000000000000),
    some (0xc028000000000000, 0xc028000000000000),
    some (0x402e000000000000, 0x402e000000000000)]
  if productBits != expected then throw (IO.userError "corner product bits differ")
  IO.println "PASS four hardware corner products (8, -10, -12, 15)"
  let sourceProducts ← cornerProducts ⟨-2.0, 3.0⟩ ⟨5.0, 7.0⟩
  let sourceBits := sourceProducts.map fun p => p.map fun q => (q.1.toBits, q.2.toBits)
  let sourceExpected : Array (Option (UInt64 × UInt64)) := #[
    some (0xc024000000000000, 0xc024000000000000),
    some (0xc02c000000000000, 0xc02c000000000000),
    some (0x402e000000000000, 0x402e000000000000),
    some (0x4035000000000000, 0x4035000000000000)]
  if sourceBits != sourceExpected then throw (IO.userError "thesis corner product bits differ")
  IO.println "PASS thesis corner products (-10, -14, 15, 21)"
  let mulCheck := checkWith multiply
  let nextOne := Float.ofBits 0x3ff0000000000001
  mulCheck "mul rounded point" ⟨nextOne, nextOne⟩ ⟨nextOne, nextOne⟩ (some (0x3ff0000000000002, 0x3ff0000000000003))
  mulCheck "mul positive underflow" ⟨tiny, tiny⟩ ⟨0.5, 0.5⟩ (some (0, 1))
  mulCheck "mul negative underflow" ⟨-tiny, -tiny⟩ ⟨0.5, 0.5⟩ (some (0x8000000000000001, 0x8000000000000000))
  mulCheck "mul overflow unknown" ⟨largest, largest⟩ ⟨2.0, 2.0⟩ none
  mulCheck "mul zero infinity unknown" ⟨0.0, 0.0⟩ ⟨inf, inf⟩ none
  mulCheck "mul mixed sign interval" ⟨-2.0, 3.0⟩ ⟨-4.0, 5.0⟩ (some (0xc028000000000000, 0x402e000000000000))
  mulCheck "mul thesis interval" ⟨-2.0, 3.0⟩ ⟨5.0, 7.0⟩ (some (0xc02c000000000000, 0x4035000000000000))
  mulCheck "mul negative intervals" ⟨-3.0, -2.0⟩ ⟨-5.0, -4.0⟩ (some (0x4020000000000000, 0x402e000000000000))
  mulCheck "mul one failed corner unknown" ⟨1.0, largest⟩ ⟨1.0, 2.0⟩ none
  let divCheck := checkWith divide
  divCheck "div positive denominator" ⟨-2.0, 3.0⟩ ⟨1.0, 2.0⟩ (some (0xc000000000000000, 0x4008000000000000))
  divCheck "div negative denominator" ⟨-2.0, 3.0⟩ ⟨-2.0, -1.0⟩ (some (0xc008000000000000, 0x4000000000000000))
  divCheck "div third rounding" one ⟨3.0, 3.0⟩ (some (0x3fd5555555555555, 0x3fd5555555555556))
  divCheck "div crossing zero unknown" one ⟨-1.0, 1.0⟩ none
  divCheck "div touching zero unknown" one ⟨0.0, 1.0⟩ none
  divCheck "div signed zero unknown" one ⟨-0.0, 0.0⟩ none
  divCheck "div positive underflow" ⟨tiny, tiny⟩ ⟨2.0, 2.0⟩ (some (0, 1))
  divCheck "div negative underflow" ⟨-tiny, -tiny⟩ ⟨2.0, 2.0⟩ (some (0x8000000000000001, 0x8000000000000000))
  divCheck "div overflow unknown" ⟨largest, largest⟩ ⟨0.5, 1.0⟩ none
  divCheck "div infinite denominator unknown" one ⟨1.0, inf⟩ none
  divCheck "div NaN numerator unknown" ⟨nan, nan⟩ one none
  let sqrtCheck := checkWith (fun a _ => squareRoot a)
  sqrtCheck "sqrt nonnegative interval" ⟨1.0, 4.0⟩ one (some (0x3ff0000000000000, 0x4000000000000000))
  sqrtCheck "sqrt irrational rounding" ⟨2.0, 2.0⟩ one (some (0x3ff6a09e667f3bcc, 0x3ff6a09e667f3bcd))
  sqrtCheck "sqrt mixed domain" ⟨-1.0, 4.0⟩ one (some (0, 0x4000000000000000))
  sqrtCheck "sqrt negative to zero" ⟨-1.0, 0.0⟩ one (some (0, 0))
  sqrtCheck "sqrt negative unknown" ⟨-4.0, -1.0⟩ one none
  sqrtCheck "sqrt signed zero" ⟨-0.0, 0.0⟩ one (some (0, 0))
  sqrtCheck "sqrt smallest subnormal" ⟨tiny, tiny⟩ one (some (0x1e60000000000000, 0x1e60000000000000))
  sqrtCheck "sqrt largest finite" ⟨largest, largest⟩ one (some (0x5fefffffffffffff, 0x5ff0000000000000))
  sqrtCheck "sqrt infinity unknown" ⟨1.0, inf⟩ one none
  sqrtCheck "sqrt negative infinity unknown" ⟨-inf, 4.0⟩ one none
  sqrtCheck "sqrt NaN lower unknown" ⟨nan, 4.0⟩ one none
  sqrtCheck "sqrt NaN upper unknown" ⟨0.0, nan⟩ one none
  sqrtCheck "sqrt reversed unknown" ⟨4.0, 1.0⟩ one none
  let badRoot ← directedSqrt (-1.0)
  unless badRoot.isNone do throw (IO.userError "negative primitive sqrt accepted")
  IO.println "PASS negative primitive sqrt rejected"
  let sineCheck := checkWith (fun a _ => sine a)
  sineCheck "sine negative input unknown" ⟨-0.1, 0.5⟩ one none
  sineCheck "sine above one unknown" ⟨0.5, nextOne⟩ one none
  sineCheck "sine reversed unknown" ⟨1.0, 0.0⟩ one none
  sineCheck "sine infinity unknown" ⟨0.0, inf⟩ one none
  sineCheck "sine NaN unknown" ⟨nan, 1.0⟩ one none
  sineCheck "sine NaN upper unknown" ⟨0.0, nan⟩ one none
  let failedSine ← GeneralizedIntervalArithmetic.HardwareSine.run
    (fun _ => true) add subtract multiply (fun _ _ => pure none)
    0.0 ⟨6.0, 6.0⟩ ⟨120.0, 120.0⟩ ⟨5040.0, 5040.0⟩ one
  unless failedSine.isNone do throw (IO.userError "sine primitive failure accepted")
  IO.println "PASS sine failed division remains unknown"
  -- Exact binary grids and underflow controls; independent rational checker reads
  -- these observed bit patterns without trusting a library sine implementation.
  let mut inputs : Array (Bounds Float) := #[⟨0.0, 0.0⟩, ⟨-0.0, 0.0⟩,
    ⟨tiny, tiny⟩, ⟨0.0, tiny⟩, ⟨0.0, 1.0⟩, ⟨0.25, 0.75⟩]
  for k in [:17] do
    let x := k.toFloat / 16.0
    inputs := inputs.push ⟨x, x⟩
    if k < 16 then inputs := inputs.push ⟨x, (k+1).toFloat / 16.0⟩
  for a in inputs do
    let some r ← sine a | throw (IO.userError "supported sine returned unknown")
    IO.println s!"SINE {a.lo.toBits} {a.hi.toBits} {r.lo.toBits} {r.hi.toBits}"
  IO.println "PASS sine supported native vectors"
  let endpointCheck := checkWith (fun a _ => sineEndpoints a)
  endpointCheck "sine endpoints below minus one unknown" ⟨-nextOne, 0.0⟩ one none
  endpointCheck "sine endpoints above one unknown" ⟨0.0, nextOne⟩ one none
  endpointCheck "sine endpoints reversed unknown" ⟨0.5, -0.5⟩ one none
  endpointCheck "sine endpoints infinity unknown" ⟨-inf, 1.0⟩ one none
  endpointCheck "sine endpoints NaN lower unknown" ⟨nan, 1.0⟩ one none
  endpointCheck "sine endpoints NaN upper unknown" ⟨-1.0, nan⟩ one none
  let failedReflection ← GeneralizedIntervalArithmetic.HardwareSine.signedPoint
    finiteLt 0.0 (fun _ _ => pure none) sine (-1.0)
  unless failedReflection.isNone do throw (IO.userError "failed reflection accepted")
  let failedPositive ← GeneralizedIntervalArithmetic.HardwareSine.signedPoint
    finiteLt 0.0 subtract (fun _ => pure none) (-1.0)
  unless failedPositive.isNone do throw (IO.userError "failed positive evaluator accepted")
  let failedUpper ← GeneralizedIntervalArithmetic.HardwareSine.endpoints
    (fun _ => true) (fun x => if finiteLt x 0.5 then pure (some (⟨0.0, 0.0⟩ : Bounds Float))
      else pure none) (⟨0.0, 1.0⟩ : Bounds Float)
  unless failedUpper.isNone do throw (IO.userError "failed upper endpoint accepted")
  IO.println "PASS sine endpoint reflection, positive and upper failure propagation"
  let mut signedInputs : Array (Bounds Float) := #[⟨-0.0, 0.0⟩, ⟨-tiny, tiny⟩,
    ⟨-tiny, -tiny⟩, ⟨0.0, tiny⟩, ⟨-1.0, 1.0⟩, ⟨-0.75, -0.25⟩,
    ⟨-0.5, 0.75⟩, ⟨0.0, 1.0⟩]
  for k in [:33] do
    let x := k.toFloat / 16.0 - 1.0
    signedInputs := signedInputs.push ⟨x, x⟩
    if k < 32 then signedInputs := signedInputs.push ⟨x, (k+1).toFloat / 16.0 - 1.0⟩
  for a in signedInputs do
    let some r ← sineEndpoints a | throw (IO.userError "supported endpoints returned unknown")
    IO.println s!"SINE_ENDPOINTS {a.lo.toBits} {a.hi.toBits} {r.lo.toBits} {r.hi.toBits}"
  IO.println "PASS sine monotone/symmetric native vectors"
  IO.println s!"PI_BOUNDS {piBounds.lo.toBits} {piBounds.hi.toBits}"
  let reducedCheck := checkWith (fun a _ => sineReduced a)
  reducedCheck "reduction near extremum unknown" ⟨1.5, 1.5⟩ one none
  reducedCheck "reduction crosses periods unknown" ⟨0.0, 7.0⟩ one none
  reducedCheck "reduction exhausted unknown" ⟨100.0, 100.0⟩ one none
  reducedCheck "reduction huge finite unknown" ⟨largest, largest⟩ one none
  reducedCheck "reduction infinity unknown" ⟨-inf, inf⟩ one none
  reducedCheck "reduction NaN unknown" ⟨nan, 0.0⟩ one none
  reducedCheck "reduction reversed unknown" ⟨7.0, 6.0⟩ one none
  let failedReduction ← GeneralizedIntervalArithmetic.HardwareSine.searchPeriods
    (fun _ _ => pure none) subtract sineEndpoints piBounds one
    (GeneralizedIntervalArithmetic.HardwareSine.periodCandidates 0.0 2.0 (-2.0) 4.0 (-4.0))
  unless failedReduction.isNone do throw (IO.userError "failed period multiplication accepted")
  IO.println "PASS failed period search remains unknown"
  let mut reducedInputs : Array (Bounds Float) := #[⟨0.0, 0.0⟩, ⟨-1.0, 1.0⟩,
    ⟨-tiny, tiny⟩, ⟨6.0, 6.5⟩, ⟨-6.5, -6.0⟩, ⟨12.25, 12.75⟩, ⟨-12.75, -12.25⟩]
  for center in #[0.0, 6.25, -6.25, 12.5, -12.5] do
    for k in [:9] do
      let x := center + k.toFloat / 8.0 - 0.5
      reducedInputs := reducedInputs.push ⟨x, x⟩
      if k < 8 then reducedInputs := reducedInputs.push ⟨x, x + 0.125⟩
  for a in reducedInputs do
    let some r ← sineReduced a | throw (IO.userError "supported reduction returned unknown")
    IO.println s!"SINE_REDUCED {a.lo.toBits} {a.hi.toBits} {r.lo.toBits} {r.hi.toBits}"
  IO.println "PASS finite whole-period sine reduction vectors"
  checkCosineQuadrants one tiny nan inf nextOne
  checkGlobal one nan inf
  unless (← roundingRestored) do throw (IO.userError "environment restoration failed")
  IO.println "PASS environment restoration"
