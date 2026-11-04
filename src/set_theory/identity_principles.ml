(* Set-Theoretic Identity Principles with Morse-Kelley Class Theory Guards *)

(* Extensionality Axiom *)
let extensionality (a: 'a set) (b: 'a set) : bool = a = b; (* Morse-Kelley Class Theory Guard *)
(* Foundation Axiom *)
let foundation (a: 'a set) : bool = not (a = []); (* Morse-Kelley Class Theory Guard *)
