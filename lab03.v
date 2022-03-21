Section lab03.

Variables A B C : Prop.

(* Exercise 1: Prove implication is transitive. What does this logical lemma correspond to in functional programming? *)
Check
  (fun (aIb : (A -> B)) (bIc : (B -> C)) => 
  (fun (a:A) => bIc (aIb a)))
: (A -> B) -> (B -> C) -> (A -> C).

(* Exercise 2: Prove conjunction is associative *)
Check
  (fun aAbAc => 
  conj (proj1 (proj1 aAbAc)) (conj (proj2 (proj1 aAbAc)) (proj2 aAbAc)))
: (A /\ B) /\ C -> A /\ (B /\ C).

(* Exercise 3: Prove disjunction distributes over conjunction: *)
Check
  (fun aVbAc => conj (match aVbAc with 
  | or_introl a => or_introl a
  | or_intror bAc => or_intror (proj1 bAc)
end) (match aVbAc with 
  | or_introl a => or_introl a
  | or_intror bAc => or_intror (proj2 bAc)
end)
) : A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).

(* Exercise 4: Prove weak form of Peirce's law holds in intuitionistic logic *)
Check
  (fun abaabb => abaabb (fun abaab => abaab (fun a => abaabb (fun ab => a))))
: ((((A -> B) -> A) -> A) -> B) -> B.

(* Exercise 5: We can always add double negation (but cannot drop it in general) *)
Check
  (fun a => (fun b => b a)) 
: A -> ~ ~ A.

(* Exercise 6: Although we can in some special cases like the following: *)
Check
  (fun f a => f (fun b => b a))
: ~ ~ ~ A -> ~ A.

(* Exercise 7: Prove we cannot add the negation of the law of excluded middle and have a sound logic.
   Keep in mind that "~ A" means "A -> False" *)
Check
  (fun a => a (or_intror (fun b => (a (or_introl b)))))
: ~ ~ (A \/ ~ A). 