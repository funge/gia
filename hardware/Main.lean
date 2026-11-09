import HardwareBounds

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

def checkWith (op : Bounds Float → Bounds Float → IO (Option (Bounds Float))) (name : String) (a b : Bounds Float) (expected : Option (UInt64 × UInt64)) : IO Unit := do
  let result ← op a b
  let bits := result.map fun r => (r.lo.toBits, r.hi.toBits)
  if bits != expected then throw (IO.userError s!"{name}: unexpected bits {repr bits}")
  IO.println s!"PASS {name}: {repr bits}"

def check := checkWith add

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
  unless (← roundingRestored) do throw (IO.userError "environment restoration failed")
  IO.println "PASS environment restoration"
