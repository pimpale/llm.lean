import LinearAlgebra.Vector
import Llm.Matmul

def compose {a b c : Type} (g : b → c) (f : a → b) : a → c :=
      g ∘ f

def main : IO Unit :=
  IO.println <| compose (fun x => x + 1) (fun x=> x * 2) 3
