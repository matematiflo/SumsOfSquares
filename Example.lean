import SumSq

def main : IO Unit :=
  IO.println s!"The sum of the list of rational numbers {([1, -2, 3/4] : List ℚ)} is {SumSq ([1, -2, 3/4] : List ℚ)}."

#eval main
