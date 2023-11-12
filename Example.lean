import SumSq

-- def  main : IO Unit :=
--   IO.println s!"The sum of squares of the list of rational numbers {([1, -2, 3/4] : List ℚ)} is {SumSq ([1, -2, 3/4] : List ℚ)}."

def main : IO Unit := do

  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "Please enter a list of integers in the form 1, -2, 3:"

  let input ← stdin.getLine
  let list := input.splitOn "," |> List.map (fun s => s.trim.toInt!)

  stdout.putStrLn s!"The list you entered is {list}. Its sum of squares is {SumSq list}."
