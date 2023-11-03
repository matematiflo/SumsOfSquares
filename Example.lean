import SumSq

def main : IO Unit :=
  IO.println s!"The sum of the list of rational numbers {([1, -2, 3/4] : List ℚ)} is {SumSq ([1, -2, 3/4] : List ℚ)}."

#eval main

/- def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "You will be asked to enter a list of integers.
First, please enter the lentgh of your list:"
  let input ← stdin.getLine
  let length := (input.dropRightWhile Char.isWhitespace).toNat!

  stdout.putStrLn s!"The length of your list is {length}."

  stdout.putStrLn "Please enter a rational number p/q (with p in ℤ and q in ℕ):"
  let input ← stdin.getLine
  let elem := (input.dropRightWhile Char.isWhitespace).toInt!

  stdout.putStrLn s!"The sum of the list of rational numbers {[elem]} is {SumSq ([elem])}."
 -/
