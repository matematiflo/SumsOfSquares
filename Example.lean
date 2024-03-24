import SumSq

import Lean

open Lean (Parsec)
open Lean.Parsec

-- def  main : IO Unit :=
--   IO.println s!"The sum of squares of the list of rational numbers {([1, -2, 3/4] : List ℚ)} is {SumSq ([1, -2, 3/4] : List ℚ)}."

-- def main : IO Unit := do

--   let stdin ← IO.getStdin
--   let stdout ← IO.getStdout

--   stdout.putStrLn "Please enter a list of integers in the form 1, -2, 3 (as many integers as you want, seperated by a comma)."

--   let input ← stdin.getLine
--   let list := input.splitOn "," |> List.map (fun s => s.trim.toInt!)

--   stdout.putStrLn s!"The list you entered is {list}. Its sum of squares is {SumSqTR list}."

def parseNat : Parsec Nat := do
  let num ← many1Chars digit
  return num.toNat!

def parsePosInt : Parsec Int := do
  let n ← parseNat
  return n

def parseNegInt : Parsec Int := do
  skipChar '-'
  let n ← parseNat
  return -n

def parseInt : Parsec Int := parsePosInt <|> parseNegInt

def parseRat : Parsec Rat := do
  let num ← parseInt
  if (← peek?) == '/' then
    skip
    let denom ← parseNat
    if denom == 0 then
      fail "Denominator is 0"
    return num / denom
  else
    return num

/--
Parses a comma-separated list of items parsed by `p`.
The commas can have whitespace surrounding them.
-/
partial def parseCommaSep {α : Type} (p : Parsec α) : Parsec (Array α) := do
  go #[]
where
  go (acc : Array α) : Parsec (Array α) := do
    let acc := acc.push (← p)
    ws
    if (← peek?) == ',' then
      skip
      ws
      go acc
    else
      return acc

def parseRatArray : Parsec (Array Rat) := do
  skipChar '['
  ws
  let arr ← parseCommaSep parseRat
  skipChar ']'
  return arr

-- Example:
#eval toString <| parseRatArray.run "[1,2/3,-3]"
/- "ok: #[1, 2/3, -3]" -/

/--
I split this out of `main` to be able to test it with `#eval`.
-/
def processLine (input : String) : IO Unit := do
  -- Uses `eof` to guarantee the whole input is read.
  let list ← IO.ofExcept <| (parseRatArray <* eof).run input.trim

  IO.println s!"The list you entered is {list}."

#eval processLine "[1, -2/3, 3]"
/-
The list you entered is #[1, -2/3, 3].
-/

def main : IO Unit := do
  let stdin ← IO.getStdin

  IO.println "Please enter a list of integers in the form [1, -2, 3] (as many integers as you want, seperated by commas)."

  let input ← stdin.getLine
  processLine input
