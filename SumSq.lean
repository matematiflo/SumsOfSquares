-- This module serves as the root of the `SumSq` library.
-- Import modules here that should be built as part of the library.
import SumSq.Defs
import SumSq.Ppties

-- #eval SumSq [1, -2, 3]

theorem ProofOf : SumSq [1, -2, 3] = 14 := by { rfl }

-- #check ProofOf

#print ProofOf
