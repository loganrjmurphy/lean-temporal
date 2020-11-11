import data.stream tactic
open stream tactic 

namespace CTL

variables AP : Type

mutual inductive state_formula, path_formula
with state_formula : Type
| T             : state_formula
| atom (a : AP) : state_formula
| conj (Φ₁ Φ₂ : state_formula ) : state_formula
| neg (Φ : state_formula) : state_formula
| E (φ : path_formula) : state_formula
| A (φ : path_formula) : state_formula
with path_formula : Type
| next (Φ : state_formula) : path_formula
| until (Φ₁ Φ₂ : state_formula) : path_formula
open state_formula
open path_formula

local notation  `∼` Φ := neg Φ
local notation Φ `&` Ψ := conj Φ Ψ
local notation `●` Φ := next Φ
local notation Φ `𝒰` Ψ := until Φ Ψ

def disj (φ ψ : state_formula AP) : state_formula AP := 
∼(∼ φ & ∼ψ)

local notation φ `⅋` ψ := disj _ φ ψ  

structure TS :=
(S : Type)
(H1 : inhabited S)
(H2 : decidable_eq S)
(Act : Type)
(TR : set (S × Act × S))
(L  : S → set AP)

def Post_of  {M : TS AP} (s : M.S) (α : M.Act) : set (M.S) := {s' | (s,α,s') ∈ M.TR}

def Post {M : TS AP} (s : M.S) : set (M.S) :=
⋃ α : M.Act, Post_of _ s α


def path {AP : Type} (M : TS AP) : Type := 
{s : stream M.S // ∀ i : ℕ, s (i + 1) ∈ Post _ (s i)}


def paths {AP : Type}
{M : TS AP} (s : M.S) : set (path M) :=
(λ π, s =  π.val.head)

mutual def state_sat, path_sat {M : TS AP}
with state_sat : state_formula AP → M.S → Prop
| T := λ _, true
| (atom a) := λ s, a ∈ M.L s
| (Φ & Ψ) := λ s, state_sat Φ s ∧ state_sat Ψ s
| (∼ Φ) := λ s, ¬ (state_sat Φ s)
| (E φ) := λ s, ∃ π : path M, π ∈ paths s ∧ path_sat φ π
| (A φ) := λ s, ∀ π : path M, π ∈ paths s → path_sat φ π
with path_sat : path_formula AP → path M → Prop
| (● Φ) := λ π, state_sat Φ (π.val 1)
| (Φ 𝒰 Ψ) := λ π, 
 ∃ j, state_sat Ψ (π.val j) ∧ (∀ k < j, state_sat Φ (π.val k))

notation s `⊨ₛ` Φ := state_sat _ Φ s
notation π `⊨ₚ ` Φ := path_sat _ Φ π


lemma disj_sat {AP : Type} {M : TS AP}  
(φ ψ : state_formula AP)(s : M.S) : 
 (s ⊨ₛ (φ ⅋ ψ)) ↔ (s ⊨ₛ φ) ∨ (s ⊨ₛ ψ) :=  
by { rw disj, repeat {rw state_sat}, finish}


def potentially (φ : state_formula AP) : state_formula AP := 
E(T 𝒰 φ)
notation `E◆` φ := potentially _ φ 

def inevitably (φ : state_formula AP) : state_formula AP := 
A(T 𝒰 φ)
notation `A◆` φ := inevitably _ φ 


def potentially_always (φ : state_formula AP) : state_formula AP := 
∼ (A◆(∼φ))
notation `E◾` φ := potentially_always _ φ 


def invariantly (φ : state_formula AP) : state_formula AP := 
∼ (E◆(∼φ))
notation `A◾` φ := invariantly _ φ 

namespace sat 

lemma potentially {AP : Type} {M : TS AP} 
(φ : state_formula AP) (s : M.S): 
(s ⊨ₛ E◆φ) ↔ ∃ π ∈ paths s, ∃ j:ℕ, (subtype.val π j) ⊨ₛ φ := 
begin 
    rw [potentially,state_sat,path_sat], dsimp only,
    split,
    { rintro ⟨π,H,j,Hj1,Hj2⟩,
      use π, exact ⟨H, ⟨j,Hj1⟩⟩},
    { rintro ⟨π,H1,j,H2⟩,
      use π, 
      split, {exact H1}, 
     {use j, split, exact H2, intros, trivial}}
end 

lemma inevitably {AP : Type} {M : TS AP} 
(φ : state_formula AP) (s : M.S) : 
(s ⊨ₛ A◆φ) ↔ ∀ π ∈ paths s, ∃ j : ℕ, (subtype.val π j) ⊨ₛ φ := 
begin
    rw [inevitably,state_sat,path_sat], dsimp only,
    split,
    { intros H1 π H2, replace H1 := H1 π H2,
      cases H1 with j H1,
      use j, exact H1.1},
    { intros H1 π H2, replace H1 := H1 π H2,
      cases H1 with j H1,
      use j, split, {exact H1}, intros, trivial}  
end  


lemma potentially_always {AP : Type} {M : TS AP}
(φ : state_formula AP) (s : M.S) : 
(s ⊨ₛ E◾φ) ↔ (∃ π ∈ paths s, ∀ j : ℕ, (subtype.val π j) ⊨ₛ φ) := 
begin 
    rw potentially_always,
    rw state_sat, dsimp only, 
    rw [inevitably,state_sat],
    simp,
end 

def invariantly {AP : Type} {M : TS AP}
(φ : state_formula AP) (s : M.S) : 
(s ⊨ₛ A◾φ) ↔ (∀ π ∈ paths s, ∀ j : ℕ, (subtype.val π j) ⊨ₛ φ) := 
begin 
    rw invariantly,
    rw state_sat, dsimp only, 
    rw [potentially,state_sat],
    simp,
end 

end sat

def sat_set {AP : Type} (M : TS AP) (φ : state_formula AP): set M.S := 
{s | s ⊨ₛ φ}

def equiv {AP : Type} (φ ψ: state_formula AP) : Prop :=  
∀ M : TS AP, (sat_set M φ) = (sat_set M ψ)

notation φ ` ≡ ` ψ := equiv φ ψ  


lemma forall_until_expansion (φ ψ : state_formula AP) : 
    A(φ 𝒰 ψ) ≡ (ψ ⅋ (φ & A●A(φ 𝒰 ψ))) := 
begin
    intro M, ext, repeat {rw sat_set}, simp,
    rw [state_sat, path_sat], simp,
    rw disj_sat, repeat {rw state_sat},
    rw path_sat, rw state_sat, rw path_sat,
    simp, sorry
end 






lemma forall_next_dual (φ : state_formula AP) : 
    (A●φ) ≡ (∼E(●∼φ)) := 
begin
    intros M, ext, repeat {rw sat_set}, simp,
    rw [state_sat,path_sat], 
    repeat {rw state_sat}, rw [path_sat, state_sat],
    simp
end 

lemma exists_next_dual (φ : state_formula AP) : 
    (E●φ) ≡ (∼A(●∼φ)) := 
begin
    intros M, ext, repeat {rw sat_set}, simp,
    rw [state_sat,path_sat],
    repeat {rw state_sat}, rw [path_sat, state_sat],
    simp
end 


lemma potentially_dual (φ : state_formula AP) : 
    (E◆φ) ≡ ∼(A◾∼φ) := 
begin 
    intros M, ext, repeat {rw sat_set}, simp,
    rw [sat.potentially,state_sat],simp,
    rw [sat.invariantly,state_sat],simp,
end 

lemma inevitably_dual (φ : state_formula AP) : 
    (A◆φ) ≡ ∼(E◾∼φ) := 
begin 
    intros M, ext, repeat {rw sat_set}, simp,
    rw [sat.inevitably,state_sat],simp,
    rw [sat.potentially_always,state_sat],simp,
end 


lemma until_dual_fst (φ ψ : state_formula AP) : 
    A(φ 𝒰 ψ) ≡ ((∼E(∼ ψ 𝒰 (∼ φ & ∼ ψ))) & ∼ E◾ ∼ψ) := 
    begin
        intros M, ext, repeat {rw sat_set}, simp,
        repeat {rw [state_sat]},
        repeat {rw [path_sat]}, simp,
        split, {
            intro H1, split,{
                intros π H2 i H3,
                repeat {rw state_sat at H3},
                rw state_sat, simp at *,
                replace H1 := H1 π H2,sorry
                 
            },{
                sorry
            }
        },{sorry}
    end 




end CTL