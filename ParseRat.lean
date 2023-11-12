import SumSq
import Std.Data.Rat.Basic

def parseRational (s : String) : Option ℚ :=
match s.splitOn "/" with
| [num, denom] =>
  let denomNat := denom.toNat!
  if denomNat = 0 then none
  else some (Rat.mk' (num.toInt!) denomNat _ _)
| _ => none

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "You will be asked to enter a list of rational numbers.
First, please enter the length of your list:"
  let input ← stdin.getLine
  let length := (input.dropRightWhile Char.isWhitespace).toNat!

  stdout.putStrLn s!"The length of your list is {length}."

  let rec readList (n : ℕ) : IO (List ℚ) := do
    if n = 0 then
      return []
    else do
      stdout.putStrLn "Please enter a rational number (numerator/denominator):"
      let input ← stdin.getLine
      match parseRational (input.dropRightWhile Char.isWhitespace) with
      | some q => do
        let rest ← readList (n - 1)
        return (q :: rest)
      | none => do
        stdout.putStrLn "Invalid input. Please enter a rational number (numerator/denominator):"
        readList n

  let list ← readList length
  stdout.putStrLn s!"The list you entered is {list}."

  stdout.putStrLn s!"The sum of the squares of the list of rational numbers {list} is {SumSq list}."
